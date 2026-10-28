-- Prove2me | solution 1 for MPSTAsync.Progress.corollary_5_30
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-28T02:10:55.166908+00:00
-- url     : https://prove2.me/submissions/929b1b21-a27c-480f-af9e-bcac6f644c0d

import Definitions.Def_MPSTAsync_Progress_Activity

set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

/-- Processes whose exposed components are receivers or empty queues. Declaration bodies and
guarded continuations do not execute until their enclosing prefix or call executes. -/
def Passive : Proc → Prop
  | .nil => True
  | .queue _ h => h = []
  | .recv _ _ _ | .branch _ _ => True
  | .par P Q => Passive P ∧ Passive Q
  | .resN _ P | .resS _ P | .defn _ P => Passive P
  | _ => False

/-- Whether a process contains a visible nonqueue action, ignoring declaration bodies. -/
def visible : Proc → Bool
  | .nil | .queue _ _ => false
  | .par P Q => visible P || visible Q
  | .resN _ P | .resS _ P | .defn _ P => visible P
  | _ => true

theorem passive_parList (ps : List Proc) :
    Passive (Proc.parList ps) ↔ ∀ P ∈ ps, Passive P := by
  induction ps with
  | nil => simp [Proc.parList, Passive]
  | cons P ps ih =>
    change (Passive P ∧ Passive (Proc.parList ps)) ↔ _
    simpa only [List.forall_mem_cons] using and_congr_right (fun _ => ih)

theorem passive_queues (ss : List Chan) : Passive (Proc.queues ss) := by
  simp [Proc.queues, passive_parList, Passive]

theorem visible_queues (ss : List Chan) : visible (Proc.queues ss) = false := by
  induction ss with
  | nil => rfl
  | cons s ss ih => simpa [Proc.queues, Proc.parList, visible] using ih

theorem passive_renameFuel (n : Nat) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (P : Proc) :
    Passive (Proc.renameFuel n ν χ ξ P) ↔ Passive P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    cases P <;> simp_all [Proc.renameFuel, Passive]

theorem visible_renameFuel (n : Nat) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (P : Proc) :
    visible (Proc.renameFuel n ν χ ξ P) = visible P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    cases P <;> simp_all [Proc.renameFuel, visible]

theorem passive_congr {P Q : Proc} (h : Congr P Q) : Passive P ↔ Passive Q := by
  induction h with
  | alpha P Q h =>
    obtain ⟨ν, χ, ξ, _, _, _, _, _, _, rfl⟩ := h
    exact (passive_renameFuel (sizeOf P) ν χ ξ P).symm
  | emptyQueues ss => simp [Passive, passive_queues]
  | _ => simp_all [Passive, and_assoc, and_comm]

theorem visible_congr {P Q : Proc} (h : Congr P Q) : visible P = visible Q := by
  induction h with
  | alpha P Q h =>
    obtain ⟨ν, χ, ξ, _, _, _, _, _, _, rfl⟩ := h
    exact (visible_renameFuel (sizeOf P) ν χ ξ P).symm
  | emptyQueues ss => simp [visible, visible_queues]
  | _ => simp_all [visible, Bool.or_assoc, Bool.or_comm]

theorem passive_no_reduction {P Q : Proc} (h : Reduces P Q) : ¬ Passive P := by
  induction h with
  | STR P P' Q' Q h₁ _ _ ih =>
    exact fun hp => ih ((passive_congr h₁).mp hp)
  | _ => simp_all [Passive]

theorem visible_not_nil {P : Proc} (h : visible P = true) : ¬ Congr P .nil := by
  intro heq
  have := visible_congr heq
  simp_all [visible]

theorem passive_of_fill (E : Ctx) (R : Proc) (h : Passive (E.fill R)) : Passive R := by
  induction E with
  | hole => exact h
  | parLeft E P ih => exact ih h.1
  | parRight P E ih => exact ih h.2
  | resN a E ih => exact ih h
  | resS ss E ih => exact ih h
  | defn D E ih => exact ih h

theorem passive_no_shared {P : Proc} (hp : Passive P) (E : Ctx) (R : Proc)
    (a : Name) (hc : Congr P (E.fill R)) (hs : SharedHead R a) : False := by
  have h := passive_of_fill E R ((passive_congr hc).mp hp)
  cases hs <;> exact h

theorem passive_reachable_eq {P Q : Proc} (hp : Passive P)
    (h : Relation.ReflTransGen Reduces P Q) : Q = P := by
  induction h with
  | refl => rfl
  | tail hstep hlast ih =>
    subst_vars
    exact False.elim (passive_no_reduction hlast hp)

theorem passive_wellLinked {P : Proc} (hp : Passive P) : WellLinked P := by
  intro Q hreach E R a hc hs
  have heq := passive_reachable_eq hp hreach
  subst Q
  exact False.elim (passive_no_shared hp E R a hc hs)

/-- The only possible exposed nonpassive operations are session initializations, whose
continuations are passive. -/
def AlmostPassive : Proc → Prop
  | .nil => True
  | .queue _ h => h = []
  | .recv _ _ _ | .branch _ _ => True
  | .request _ _ _ P | .accept _ _ _ P => Passive P
  | .par P Q => AlmostPassive P ∧ AlmostPassive Q
  | .resN _ P | .resS _ P | .defn _ P => AlmostPassive P
  | _ => False

/-- Number of exposed shared-name prefixes; guarded continuations do not contribute. -/
def sharedCount : Proc → Nat
  | .request _ _ _ _ | .accept _ _ _ _ => 1
  | .par P Q => sharedCount P + sharedCount Q
  | .resN _ P | .resS _ P | .defn _ P => sharedCount P
  | _ => 0

theorem almostPassive_parList (ps : List Proc) :
    AlmostPassive (Proc.parList ps) ↔ ∀ P ∈ ps, AlmostPassive P := by
  induction ps with
  | nil => simp [Proc.parList, AlmostPassive]
  | cons P ps ih =>
    change (AlmostPassive P ∧ AlmostPassive (Proc.parList ps)) ↔ _
    simpa only [List.forall_mem_cons] using and_congr_right (fun _ => ih)

theorem almostPassive_queues (ss : List Chan) : AlmostPassive (Proc.queues ss) := by
  simp [Proc.queues, almostPassive_parList, AlmostPassive]

theorem sharedCount_parList (ps : List Proc) :
    sharedCount (Proc.parList ps) = (ps.map sharedCount).sum := by
  induction ps with
  | nil => rfl
  | cons P ps ih => simpa [Proc.parList, sharedCount] using congrArg (sharedCount P + ·) ih

theorem sharedCount_queues (ss : List Chan) : sharedCount (Proc.queues ss) = 0 := by
  simp [Proc.queues, sharedCount_parList, Function.comp_def, sharedCount]

theorem almostPassive_renameFuel (n : Nat) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (P : Proc) :
    AlmostPassive (Proc.renameFuel n ν χ ξ P) ↔ AlmostPassive P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    cases P <;> simp_all [Proc.renameFuel, AlmostPassive, passive_renameFuel]

theorem sharedCount_renameFuel (n : Nat) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (P : Proc) :
    sharedCount (Proc.renameFuel n ν χ ξ P) = sharedCount P := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih => cases P <;> simp_all [Proc.renameFuel, sharedCount]

theorem almostPassive_congr {P Q : Proc} (h : Congr P Q) :
    AlmostPassive P ↔ AlmostPassive Q := by
  induction h with
  | alpha P Q h =>
    obtain ⟨ν, χ, ξ, _, _, _, _, _, _, rfl⟩ := h
    exact (almostPassive_renameFuel (sizeOf P) ν χ ξ P).symm
  | emptyQueues ss => simp [AlmostPassive, almostPassive_queues]
  | request a n ss P Q h _ => exact passive_congr h
  | accept a p ss P Q h _ => exact passive_congr h
  | _ => simp_all [AlmostPassive, and_assoc, and_comm]

theorem sharedCount_congr {P Q : Proc} (h : Congr P Q) :
    sharedCount P = sharedCount Q := by
  induction h with
  | alpha P Q h =>
    obtain ⟨ν, χ, ξ, _, _, _, _, _, _, rfl⟩ := h
    exact (sharedCount_renameFuel (sizeOf P) ν χ ξ P).symm
  | emptyQueues ss => simp [sharedCount, sharedCount_queues]
  | _ => simp_all [sharedCount, Nat.add_assoc, Nat.add_comm]

theorem almostPassive_zero (P : Proc) (h : AlmostPassive P) (hc : sharedCount P = 0) :
    Passive P := by
  cases P with
  | par P Q =>
    have hs : sharedCount P = 0 ∧ sharedCount Q = 0 := Nat.add_eq_zero_iff.mp hc
    exact ⟨almostPassive_zero P h.1 hs.1, almostPassive_zero Q h.2 hs.2⟩
  | resN a P => exact almostPassive_zero P h hc
  | resS ss P => exact almostPassive_zero P h hc
  | defn D P => exact almostPassive_zero P h hc
  | request _ _ _ _ | accept _ _ _ _ => simp [sharedCount] at hc
  | _ => exact h
termination_by sizeOf P

theorem almostPassive_reduction {P Q : Proc} (hstep : Reduces P Q) :
    AlmostPassive P → sharedCount P ≤ 2 → Passive Q ∧ 2 ≤ sharedCount P := by
  induction hstep with
  | LINK a n ss P ps hn hs =>
    intro hp hc
    have hP : Passive P := hp.1
    have hps : ∀ i, Passive (ps i) := by
      intro i
      have hmem : Proc.accept a (i.val+2) ss (ps i) ∈
          List.ofFn (fun i : Fin (n-1) => Proc.accept a (i.val+2) ss (ps i)) :=
        List.mem_ofFn.mpr ⟨i, rfl⟩
      exact (almostPassive_parList _).mp hp.2 _ hmem
    constructor
    · simp [Passive, passive_parList, passive_queues, hP, hps]
    · simp [sharedCount, sharedCount_parList, Function.comp_def]
      omega
  | SCOPN a P Q h ih => exact ih
  | SCOPS ss P Q h ih => exact ih
  | DEFIN D P Q h ih => exact ih
  | PAR P P' Q h ih =>
    intro hp hc
    have hpcount : sharedCount P ≤ 2 := by change sharedCount P + sharedCount Q ≤ 2 at hc; omega
    obtain ⟨hP', hPcount⟩ := ih hp.1 hpcount
    have hQcount : sharedCount Q = 0 := by
      change sharedCount P + sharedCount Q ≤ 2 at hc
      omega
    exact ⟨⟨hP', almostPassive_zero Q hp.2 hQcount⟩, by
      change 2 ≤ sharedCount P + sharedCount Q
      omega⟩
  | STR P P' Q' Q hcP h hcQ ih =>
    intro hp hc
    have hc' : sharedCount P' ≤ 2 := by simpa [← sharedCount_congr hcP] using hc
    obtain ⟨hq', hcP'⟩ := ih ((almostPassive_congr hcP).mp hp) hc'
    exact ⟨(passive_congr hcQ).mp hq', by simpa [sharedCount_congr hcP] using hcP'⟩
  | _ => simp_all [AlmostPassive]

theorem almostPassive_reachable {P Q : Proc} (hp : AlmostPassive P)
    (hc : sharedCount P ≤ 2) (h : Relation.ReflTransGen Reduces P Q) :
    Q = P ∨ Passive Q := by
  induction h with
  | refl => exact Or.inl rfl
  | tail hreach hstep ih =>
    rcases ih with rfl | hpass
    · exact Or.inr (almostPassive_reduction hstep hp hc).1
    · exact False.elim (passive_no_reduction hstep hpass)

theorem almostPassive_wellLinked {P : Proc} (hp : AlmostPassive P)
    (hc : sharedCount P ≤ 2)
    (hinit : ∀ (E : Ctx) (R : Proc) (a : Name),
      Congr P (E.fill R) → SharedHead R a →
      ∃ (E' : Ctx) (S : Proc), Congr P (E'.fill S) ∧ SharedRedexContains R S a) :
    WellLinked P := by
  intro Q hreach E R a hcon hhead
  rcases almostPassive_reachable hp hc hreach with rfl | hpass
  · exact hinit E R a hcon hhead
  · exact False.elim (passive_no_shared hpass E R a hcon hhead)

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

def omegaType : EType := .mu 0 (.var 0)

theorem stop_equiv_omega : EEquiv .stop omegaType := by
  refine ⟨{(.stop, omegaType)}, by simp, ?_⟩
  intro A B h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h)
  simp [BisimStep, omegaType, EType.substE, EType.substEFuel]

theorem omega_equiv (T : EType) : EEquiv omegaType T := by
  refine ⟨{(omegaType, T)}, by simp, ?_⟩
  intro A B h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Set.mem_singleton_iff.mp h)
  simp [BisimStep, omegaType, EType.substE, EType.substEFuel]

theorem single_wf (T : EType) (p : Role) :
    Typing.WellFormed [([0], [(.pure T, p)])] := by
  simp [Typing.WellFormed, HFamily.WellFormed]

theorem single_equiv (T U : EType) (p : Role) (h : EEquiv T U) :
    TypingEquiv [([0], [(.pure T, p)])] [([0], [(.pure U, p)])] := by
  simpa [TypingEquiv, HFamilyEquiv, HFamily.roles] using h

/-- The runtime conversion rule admits any endpoint type for inaction, via an
unguarded intermediate type which runtime well-formedness does not exclude. -/
theorem nil_any_endpoint (Γ : Env) (T : EType) (p : Role) :
    RTypedSimple Γ .nil [] [([0], [(.pure T, p)])] := by
  have hnil : RTypedSimple Γ .nil [] [([0], [(.pure .stop, p)])] :=
    .INACT _ _ (by simp [Typing.EndOnly, Typing.WellFormed, HFamily.WellFormed])
      (by simp)
  have hloop := RTypedSimple.CONV Γ .nil [] _ _
    (single_equiv _ _ p stop_equiv_omega) (single_wf omegaType p) hnil
  exact .CONV _ _ _ _ _ (single_equiv _ _ p (omega_equiv T)) (single_wf T p) hloop

def protocol : GType := .comm 1 2 1 (.sorts []) .stop
def sendType : EType := .send 1 (.sorts []) .stop
def recvType : EType := .recv 1 (.sorts []) .stop
def environment : Env := ⟨[(0, .shared protocol)], []⟩
def receiver : Proc := .recv 0 [] .nil
def requester : Proc := .request 0 2 [0] .nil
def accepter : Proc := .accept 0 2 [0] receiver
def initial : Proc := .par requester (.par accepter .nil)
def stuck : Proc :=
  .resS [0] (.par (.par .nil (.par receiver .nil)) (.par (.queue 0 []) .nil))

theorem protocol_no_prec (n m : Pos) (h : PrecStep protocol n m) : False := by
  cases h <;> rename_i h <;> cases h

theorem protocol_coherent : Coherent protocol := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [protocol, GType.WellFormed, GType.wfFuel, VType.wfFuel]
  · constructor
    · intro n
      have hunfold : protocol.unfold n = protocol := by
        simp [protocol, GType.unfold, GType.unfoldFuel]
      rw [hunfold]
      intro a b p q r s k ha hb hab
      have impossible : False := by
        induction hab with
        | single h => exact protocol_no_prec _ _ h
        | tail _ h _ => exact protocol_no_prec _ _ h
      exact impossible.elim
    · simp [protocol, GType.allCarried, GType.allCarriedFuel, VType.allCarriedFuel]
  · intro p hp
    simp [protocol, GType.pid, GType.pidFuel] at hp
    rcases hp with rfl | rfl
    · exact ⟨sendType, rfl⟩
    · exact ⟨recvType, rfl⟩
  · simp [protocol, GType.allCarried, GType.allCarriedFuel, VType.allCarriedFuel]

theorem environment_wf : environment.WellFormed := by
  simpa [environment, Env.WellFormed, ValSort.WellFormed] using protocol_coherent

theorem empty_end : Typing.EndOnly [] := by
  simp [Typing.EndOnly, Typing.WellFormed]

theorem empty_comp : TypingComp [] [] [] := by
  simp [TypingComp, Typing.WellFormed]

theorem receiver_typed :
    RTypedSimple environment receiver [] [([0], [(.pure recvType, 2)])] := by
  apply RTypedSimple.RCV environment 0 [] [] .nil
    [([0], [(.pure .stop, 2)])] _ [0] 1 2 .stop
  · simp [TypeAt]
  · rfl
  · simp
  · simp
  · exact ⟨[], [], rfl, rfl⟩
  · simp
  · exact .INACT _ _
      (by simp [Typing.EndOnly, Typing.WellFormed, HFamily.WellFormed]) (by simp)

theorem requester_typed : RTypedSimple environment requester [] [] := by
  apply RTypedSimple.MCAST environment 0 2 [0] .nil []
    [([0], [(.pure sendType, 1)])] protocol sendType
  · simp [environment]
  · decide
  · decide
  · decide
  · decide
  · rfl
  · simp [Typing.Insert, Typing.chans]
  · rfl
  · exact nil_any_endpoint _ _ _

theorem accepter_typed : RTypedSimple environment accepter [] [] := by
  apply RTypedSimple.MACC environment 0 2 [0] receiver []
    [([0], [(.pure recvType, 2)])] protocol recvType
  · simp [environment]
  · decide
  · decide
  · decide
  · rfl
  · simp [Typing.Insert, Typing.chans]
  · rfl
  · exact receiver_typed

theorem initial_typed : RTypedSimple environment initial [] [] := by
  have hn : RTypedSimple environment .nil [] [] := .INACT _ _ empty_end (by simp)
  have ha := RTypedSimple.CONC _ _ _ [] [] [] [] [] (by simp) (by simp)
    empty_comp accepter_typed hn
  exact .CONC _ _ _ [] [] [] [] [] (by simp) (by simp) empty_comp requester_typed ha

theorem initial_program : IsProgram initial := by
  refine ⟨initial, .refl _, ?_, ?_, ?_, ?_⟩ <;>
    simp [initial, requester, accepter, receiver, Proc.noQueues, Proc.noQueuesFuel,
      Proc.noResS, Proc.noResSFuel, Proc.freeChans, Proc.freeChansFuel,
      Proc.freePVars, Proc.freePVarsFuel]

theorem initial_shared :
    ∀ a ∈ initial.freeNames, ∃ G, (a, ValSort.shared G) ∈ environment.names := by
  intro a ha
  have : a = 0 := by
    simpa [initial, requester, accepter, receiver, Proc.freeNames, Proc.freeNamesFuel]
      using ha
  subst a
  exact ⟨protocol, by simp [environment]⟩

theorem initial_step : Reduces initial stuck := by
  exact Reduces.LINK 0 2 [0] .nil (fun _ ↦ receiver) (by decide) (by decide)

theorem typing_comp_empty_right (Δ : Typing) (h : Δ.WellFormed) : TypingComp Δ [] Δ := by
  refine ⟨h, by simp [Typing.WellFormed], h, by simp, ?_, by simp⟩
  intro x hx
  exact Or.inl ⟨x, hx, rfl, by simp, rfl⟩

theorem single_family_wf (F : HFamily) (h : F.WellFormed) :
    Typing.WellFormed [([0], F)] := by
  simpa [Typing.WellFormed] using h

theorem single_comp (F H K : HFamily) (h : HFamilyComp F H K) :
    TypingComp [([0], F)] [([0], H)] [([0], K)] := by
  refine ⟨single_family_wf F h.1, single_family_wf H h.2.1,
    single_family_wf K h.2.2.1, ?_, ?_, by simp⟩
  · simp
  · intro x hx
    have hx' : x = ([0], K) := by simpa using hx
    subst x
    exact Or.inr (Or.inr ⟨([0], F), by simp, ([0], H), by simp, rfl, rfl, h⟩)

def endpoints : HFamily := [(.pure sendType, 1), (.pure recvType, 2)]

theorem endpoints_comp :
    HFamilyComp [(.pure sendType, 1)] [(.pure recvType, 2)] endpoints := by
  simp [HFamilyComp, HFamily.WellFormed, HFamily.roles, endpoints]

theorem family_comp_empty_right (F : HFamily) (h : F.WellFormed) :
    HFamilyComp F [] F := by
  refine ⟨h, by simp [HFamily.WellFormed], h, by simp [HFamily.roles], ?_⟩
  intro x hx
  exact Or.inl ⟨x, hx, rfl, by simp [HFamily.roles], rfl⟩

theorem send_equiv_self : EEquiv sendType sendType := by
  refine ⟨{(sendType, sendType), (.stop, .stop)}, by simp, ?_⟩
  intro A B h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [BisimStep, sendType]

theorem recv_equiv_self : EEquiv recvType recvType := by
  refine ⟨{(recvType, recvType), (.stop, .stop)}, by simp, ?_⟩
  intro A B h
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at h
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [BisimStep, recvType]

theorem endpoints_coherent : HFamilyCoherent endpoints := by
  refine ⟨[(sendType, 1), (recvType, 2)], ?_, by simp [endpoints, HFamily.roles,
    Family.roles], ?_⟩
  · constructor
    · simp [Family.WellFormed, EType.WellFormed, EType.wfFuel, VType.wfFuel,
        sendType, recvType]
    · refine ⟨protocol, protocol_coherent, ?_, ?_⟩
      · decide
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact ⟨sendType, rfl, send_equiv_self⟩
        · exact ⟨recvType, rfl, recv_equiv_self⟩
  · intro x hx
    simp only [endpoints, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact ⟨(sendType, 1), by simp, rfl, rfl⟩
    · exact ⟨(recvType, 2), by simp, rfl, rfl⟩

theorem stuck_typed : RTypedSimple environment stuck [] [] := by
  have hn : RTypedSimple environment .nil [] [] := .INACT _ _ empty_end (by simp)
  have hr := RTypedSimple.CONC _ _ _ [] [] _ [] _ (by simp) (by simp)
    (typing_comp_empty_right _ (single_wf recvType 2)) receiver_typed hn
  have hs := RTypedSimple.CONC _ _ _ [] [] _ _ _ (by simp) (by simp)
    (single_comp _ _ _ endpoints_comp) (nil_any_endpoint environment sendType 1) hr
  have hq : RTypedSimple environment (.queue 0 []) [0] [([0], [])] := by
    apply RTypedSimple.QNIL environment [0] 1 0 [] [] _ (by simp [TypeAt]) (by simp) empty_end
    exact typing_comp_empty_right _ (single_family_wf [] (by simp [HFamily.WellFormed]))
  have hqn := RTypedSimple.CONC _ _ _ [0] [] _ [] _ (by simp) (by simp)
    (typing_comp_empty_right _ (single_family_wf [] (by simp [HFamily.WellFormed]))) hq hn
  have hall := RTypedSimple.CONC _ _ _ [] [0] _ _ _ (by simp) (by simp)
    (single_comp _ _ _ (family_comp_empty_right endpoints endpoints_comp.2.2.1)) hs hqn
  exact .CRES _ [0] _ [0] endpoints _ [] (by simp) rfl endpoints_coherent hall

end MPSTAsync.Progress.Counterexample




set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

def freeSharedCount (P : Proc) (a : Name) : Nat :=
  match P with
  | .request b _ _ _ | .accept b _ _ _ => if a = b then 1 else 0
  | .par P Q => freeSharedCount P a + freeSharedCount Q a
  | .resN b P => if a = b then 0 else freeSharedCount P a
  | .resS _ P | .defn _ P => freeSharedCount P a
  | _ => 0

theorem freeSharedCount_le (P : Proc) (a : Name) : freeSharedCount P a ≤ sharedCount P := by
  cases P <;> simp only [freeSharedCount, sharedCount]
  all_goals first
    | omega
    | exact Nat.add_le_add (freeSharedCount_le _ _) (freeSharedCount_le _ _)
    | exact freeSharedCount_le _ _
    | split <;> first | omega | exact freeSharedCount_le _ _
termination_by sizeOf P

theorem freeSharedCount_pos_namesFuel (fuel : Nat) (P : Proc) (a : Name)
    (hfuel : sizeOf P ≤ fuel) (hpos : 0 < freeSharedCount P a) :
    a ∈ Proc.freeNamesFuel fuel P := by
  cases fuel with
  | zero => cases P <;> simp at hfuel
  | succ fuel =>
    cases P <;> simp only [freeSharedCount] at hpos
    all_goals try omega
    case request b n ss P =>
      split at hpos <;> simp_all [Proc.freeNamesFuel]
    case accept b p ss P =>
      split at hpos <;> simp_all [Proc.freeNamesFuel]
    case par P Q =>
      have hP : sizeOf P ≤ fuel := by simp_all; omega
      have hQ : sizeOf Q ≤ fuel := by simp_all; omega
      rcases (show 0 < freeSharedCount P a ∨ 0 < freeSharedCount Q a by omega) with hp | hq
      · exact Finset.mem_union_left _ (freeSharedCount_pos_namesFuel fuel P a hP hp)
      · exact Finset.mem_union_right _ (freeSharedCount_pos_namesFuel fuel Q a hQ hq)
    case resN b P =>
      split at hpos
      · omega
      · rename_i hab
        have hP : sizeOf P ≤ fuel := by simp_all; omega
        exact Finset.mem_erase.mpr ⟨hab, freeSharedCount_pos_namesFuel fuel P a hP hpos⟩
    case resS ss P =>
      have hP : sizeOf P ≤ fuel := by simp_all; omega
      exact freeSharedCount_pos_namesFuel fuel P a hP hpos
    case defn D P =>
      have hP : sizeOf P ≤ fuel := by simp_all; omega
      exact Finset.mem_union_left _ (freeSharedCount_pos_namesFuel fuel P a hP hpos)
termination_by fuel

theorem freeSharedCount_pos_names {P : Proc} {a : Name}
    (hpos : 0 < freeSharedCount P a) : a ∈ P.freeNames :=
  freeSharedCount_pos_namesFuel (sizeOf P) P a le_rfl hpos

theorem freeSharedCount_renameFuel (fuel : Nat) (P : Proc) (a : Name)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hν : Function.Injective ν) (hfuel : sizeOf P ≤ fuel) :
    freeSharedCount (Proc.renameFuel fuel ν χ ξ P) (ν a) = freeSharedCount P a := by
  cases fuel with
  | zero => cases P <;> simp at hfuel
  | succ fuel =>
    cases P <;> simp only [Proc.renameFuel, freeSharedCount]
    all_goals try simp only [hν.eq_iff]
    case par P Q =>
      rw [freeSharedCount_renameFuel fuel P a ν χ ξ hν (by simp_all; omega),
        freeSharedCount_renameFuel fuel Q a ν χ ξ hν (by simp_all; omega)]
    case resN b P =>
      split <;> try rfl
      exact freeSharedCount_renameFuel fuel P a ν χ ξ hν (by simp_all; omega)
    case resS ss P =>
      exact freeSharedCount_renameFuel fuel P a ν χ ξ hν (by simp_all; omega)
    case defn D P =>
      exact freeSharedCount_renameFuel fuel P a ν χ ξ hν (by simp_all; omega)
termination_by fuel

theorem freeSharedCount_alpha {P Q : Proc} (h : Alpha P Q) (a : Name) :
    freeSharedCount P a = freeSharedCount Q a := by
  obtain ⟨ν, χ, ξ, hν, _, _, hfix, _, _, rfl⟩ := h
  obtain ⟨b, rfl⟩ := hν.2 a
  rw [Proc.rename, freeSharedCount_renameFuel _ _ _ _ _ _ hν.1 le_rfl]
  by_cases hb : freeSharedCount P b = 0
  · rw [hb]
    by_contra hn
    have hp : 0 < freeSharedCount P (ν b) := by omega
    have heq := hfix (ν b) (freeSharedCount_pos_names hp)
    have hid : ν b = b := hν.1 heq
    simp_all
  · have hp : 0 < freeSharedCount P b := by omega
    rw [hfix b (freeSharedCount_pos_names hp)]

theorem freeSharedCount_queues (ss : List Chan) (a : Name) :
    freeSharedCount (Proc.queues ss) a = 0 := by
  induction ss with
  | nil => rfl
  | cons c ss ih => simpa [Proc.queues, Proc.parList, freeSharedCount] using ih

theorem freeSharedCount_congr {P Q : Proc} (h : Congr P Q) (a : Name) :
    freeSharedCount P a = freeSharedCount Q a := by
  induction h with
  | alpha P Q h => exact freeSharedCount_alpha h a
  | scopeN b P Q hfresh =>
    have hz : freeSharedCount Q b = 0 := by
      by_contra hn
      exact hfresh (freeSharedCount_pos_names (by omega))
    by_cases hab : a = b <;> simp_all [freeSharedCount]
  | emptyQueues ss => simp [freeSharedCount, freeSharedCount_queues]
  | resNN b c P =>
    simp only [freeSharedCount]
    split <;> split <;> simp_all
  | _ => simp_all [freeSharedCount, Nat.add_assoc, Nat.add_comm]

theorem sharedCount_le_fill (E : Ctx) (R : Proc) :
    sharedCount R ≤ sharedCount (E.fill R) := by
  induction E with
  | hole => exact le_rfl
  | parLeft E P ih => simpa [Ctx.fill, sharedCount] using ih.trans (Nat.le_add_right _ _)
  | parRight P E ih => simpa [Ctx.fill, sharedCount] using ih.trans (Nat.le_add_left _ _)
  | resN a E ih | resS ss E ih | defn D E ih => exact ih

theorem freeSharedCount_full_of_fill (E : Ctx) (R : Proc) (a : Name)
    (hfull : freeSharedCount (E.fill R) a = sharedCount (E.fill R)) :
    freeSharedCount R a = sharedCount R := by
  induction E with
  | hole => exact hfull
  | parLeft E P ih =>
    apply ih
    have h₁ := freeSharedCount_le (E.fill R) a
    have h₂ := freeSharedCount_le P a
    simp only [Ctx.fill, freeSharedCount, sharedCount] at hfull
    omega
  | parRight P E ih =>
    apply ih
    have h₁ := freeSharedCount_le P a
    have h₂ := freeSharedCount_le (E.fill R) a
    simp only [Ctx.fill, freeSharedCount, sharedCount] at hfull
    omega
  | resN b E ih =>
    simp only [Ctx.fill, freeSharedCount, sharedCount] at hfull
    split at hfull
    · have h₁ := sharedCount_le_fill E R
      have h₂ := freeSharedCount_le R a
      omega
    · exact ih hfull
  | resS ss E ih | defn D E ih => exact ih hfull

theorem sharedHead_subject_of_full_count (P : Proc) (a : Name)
    (hfull : freeSharedCount P a = sharedCount P)
    (E : Ctx) (R : Proc) (b : Name) (hc : Congr P (E.fill R))
    (hs : SharedHead R b) : b = a := by
  have hc' : freeSharedCount (E.fill R) a = sharedCount (E.fill R) := by
    rw [← freeSharedCount_congr hc a, ← sharedCount_congr hc]
    exact hfull
  have hr := freeSharedCount_full_of_fill E R a hc'
  cases hs <;> simp only [freeSharedCount, sharedCount] at hr
  all_goals split at hr <;> simp_all

def SharedParameters : Proc → Prop
  | .request _ n ss _ => n = 2 ∧ ss.length = 1
  | .accept _ p ss _ => p = 2 ∧ ss.length = 1
  | .par P Q => SharedParameters P ∧ SharedParameters Q
  | .resN _ P | .resS _ P | .defn _ P => SharedParameters P
  | _ => True

theorem sharedParameters_renameFuel (fuel : Nat) (ν : Name → Name)
    (χ : Chan → Chan) (ξ : PVar → PVar) (P : Proc) :
    SharedParameters (Proc.renameFuel fuel ν χ ξ P) ↔ SharedParameters P := by
  induction fuel generalizing P with
  | zero => rfl
  | succ fuel ih => cases P <;> simp_all [Proc.renameFuel, SharedParameters]

theorem sharedParameters_queues (ss : List Chan) : SharedParameters (Proc.queues ss) := by
  induction ss with
  | nil => trivial
  | cons c ss ih => exact ⟨trivial, ih⟩

theorem sharedParameters_congr {P Q : Proc} (h : Congr P Q) :
    SharedParameters P ↔ SharedParameters Q := by
  induction h with
  | alpha P Q h =>
    obtain ⟨ν, χ, ξ, _, _, _, _, _, _, rfl⟩ := h
    exact (sharedParameters_renameFuel (sizeOf P) ν χ ξ P).symm
  | emptyQueues ss => simp [SharedParameters, sharedParameters_queues]
  | _ => simp_all [SharedParameters, and_assoc, and_comm]

theorem sharedParameters_of_fill (E : Ctx) (R : Proc)
    (h : SharedParameters (E.fill R)) : SharedParameters R := by
  induction E with
  | hole => exact h
  | parLeft E P ih => exact ih h.1
  | parRight P E ih => exact ih h.2
  | resN a E ih | resS ss E ih | defn D E ih => exact ih h

def GoodSharedHeads : Proc → Prop
  | .request _ n ss B => n = 2 ∧ ∃ c, ss = [c] ∧ Congr B .nil
  | .accept _ p ss B => p = 2 ∧ ∃ c, ss = [c] ∧ Congr B (.recv c [] .nil)
  | .par P Q => GoodSharedHeads P ∧ GoodSharedHeads Q
  | .resN _ P | .resS _ P | .defn _ P => GoodSharedHeads P
  | _ => True

theorem goodSharedHeads_queues (ss : List Chan) : GoodSharedHeads (Proc.queues ss) := by
  induction ss with
  | nil => trivial
  | cons c ss ih => exact ⟨trivial, ih⟩

theorem congr_target_iff {P Q R : Proc} (h : Congr P Q) : Congr P R ↔ Congr Q R :=
  ⟨fun hp => .trans _ _ _ (.symm _ _ h) hp, fun hq => .trans _ _ _ h hq⟩

/-- Alpha-conversion transport is isolated from the elementary congruence cases. -/
theorem goodSharedHeads_congr_of_alpha
    (hα : ∀ P Q, Alpha P Q → (GoodSharedHeads P ↔ GoodSharedHeads Q))
    {P Q : Proc} (h : Congr P Q) : GoodSharedHeads P ↔ GoodSharedHeads Q := by
  induction h with
  | alpha P Q h => exact hα P Q h
  | request a n ss P Q h ih =>
    simp only [GoodSharedHeads]
    exact and_congr_right (fun _ => exists_congr (fun c =>
      and_congr_right (fun _ => congr_target_iff h)))
  | accept a p ss P Q h ih =>
    simp only [GoodSharedHeads]
    exact and_congr_right (fun _ => exists_congr (fun c =>
      and_congr_right (fun _ => congr_target_iff h)))
  | emptyQueues ss => simp [GoodSharedHeads, goodSharedHeads_queues]
  | _ => simp_all [GoodSharedHeads, and_assoc, and_comm]

theorem goodSharedHeads_of_fill (E : Ctx) (R : Proc)
    (h : GoodSharedHeads (E.fill R)) : GoodSharedHeads R := by
  induction E with
  | hole => exact h
  | parLeft E P ih => exact ih h.1
  | parRight P E ih => exact ih h.2
  | resN a E ih | resS ss E ih | defn D E ih => exact ih h

theorem request_singleton_channel_congr (c : Chan) :
    Congr (.request 0 2 [c] .nil) (.request 0 2 [0] .nil) := by
  apply Congr.alpha
  refine ⟨id, Equiv.swap c 0, id, Function.bijective_id, (Equiv.swap c 0).bijective,
    Function.bijective_id, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rfl
  · simp [Proc.freeChans, Proc.freeChansFuel]
  · intro X hX
    rfl
  · simp [Proc.rename, Proc.renameFuel]

private theorem freeChansFuel_nil (fuel : Nat) : Proc.freeChansFuel fuel .nil = ∅ := by
  cases fuel <;> rfl

private theorem renameFuel_nil (fuel : Nat) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) : Proc.renameFuel fuel ν χ ξ .nil = .nil := by
  cases fuel <;> rfl

theorem accept_singleton_channel_congr (c : Chan) :
    Congr (.accept 0 2 [c] (.recv c [] .nil))
      (.accept 0 2 [0] (.recv 0 [] .nil)) := by
  apply Congr.alpha
  refine ⟨id, Equiv.swap c 0, id, Function.bijective_id, (Equiv.swap c 0).bijective,
    Function.bijective_id, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rfl
  · simp [Proc.freeChans, Proc.freeChansFuel, freeChansFuel_nil]
  · intro X hX
    rfl
  · simp [Proc.rename, Proc.renameFuel, renameFuel_nil]

theorem goodSharedHead_canonical {R : Proc} (hs : SharedHead R 0) (hg : GoodSharedHeads R) :
    Congr R (.request 0 2 [0] .nil) ∨
      Congr R (.accept 0 2 [0] (.recv 0 [] .nil)) := by
  cases hs with
  | request a n ss B =>
    obtain ⟨rfl, c, rfl, hB⟩ := hg
    exact Or.inl (.trans _ _ _ (.request _ _ _ _ _ hB) (request_singleton_channel_congr c))
  | accept a p ss B =>
    obtain ⟨rfl, c, rfl, hB⟩ := hg
    exact Or.inr (.trans _ _ _ (.accept _ _ _ _ _ hB) (accept_singleton_channel_congr c))

/-- The two structural-congruence orbits needed by the concrete progress witness. -/
def SimpleTargetRename (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) : Prop :=
  (∀ (fuel : Nat) (P : Proc), sizeOf P ≤ fuel →
    (Congr (Proc.renameFuel fuel ν χ ξ P) .nil ↔ Congr P .nil)) ∧
  (∀ (fuel : Nat) (P : Proc) (c : Chan), sizeOf P ≤ fuel →
    (Congr (Proc.renameFuel fuel ν χ ξ P) (.recv (χ c) [] .nil) ↔
      Congr P (.recv c [] .nil)))

theorem goodSharedHeads_renameFuel (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (ht : SimpleTargetRename ν χ ξ) (fuel : Nat) (P : Proc) (hfuel : sizeOf P ≤ fuel) :
    GoodSharedHeads (Proc.renameFuel fuel ν χ ξ P) ↔ GoodSharedHeads P := by
  cases fuel with
  | zero => cases P <;> simp at hfuel
  | succ fuel =>
    cases P <;> simp only [Proc.renameFuel, GoodSharedHeads]
    case request a n ss B =>
      have hn := ht.1 fuel B (by simp_all; omega)
      constructor
      · rintro ⟨hp, d, hs, hB⟩
        obtain ⟨c, hc, hcd⟩ := List.map_eq_singleton_iff.mp hs
        exact ⟨hp, c, hc, hn.mp hB⟩
      · rintro ⟨hp, c, rfl, hB⟩
        exact ⟨hp, χ c, rfl, hn.mpr hB⟩
    case accept a p ss B =>
      have hn := ht.2 fuel B
      have hBfuel : sizeOf B ≤ fuel := by simp_all; omega
      constructor
      · rintro ⟨hp, d, hs, hB⟩
        obtain ⟨c, hc, hcd⟩ := List.map_eq_singleton_iff.mp hs
        subst d
        exact ⟨hp, c, hc, (hn c hBfuel).mp hB⟩
      · rintro ⟨hp, c, rfl, hB⟩
        exact ⟨hp, χ c, rfl, (hn c hBfuel).mpr hB⟩
    case par P Q =>
      exact and_congr
        (goodSharedHeads_renameFuel ν χ ξ ht fuel P (by simp_all; omega))
        (goodSharedHeads_renameFuel ν χ ξ ht fuel Q (by simp_all; omega))
    case resN a P | resS ss P | defn D P =>
      exact goodSharedHeads_renameFuel ν χ ξ ht fuel P (by simp_all; omega)
termination_by fuel

theorem goodSharedHeads_alpha_of_transport
    (ht : ∀ (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar),
      Function.Bijective ν → Function.Bijective χ → Function.Bijective ξ →
        SimpleTargetRename ν χ ξ)
    (P Q : Proc) (h : Alpha P Q) : GoodSharedHeads P ↔ GoodSharedHeads Q := by
  obtain ⟨ν, χ, ξ, hν, hχ, hξ, _, _, _, rfl⟩ := h
  exact (goodSharedHeads_renameFuel ν χ ξ (ht ν χ ξ hν hχ hξ) (sizeOf P) P le_rfl).symm

/-- If every actual step enters the passive fragment, the quantified reachability clause in
well-linkedness reduces to the occurrence condition at the initial process itself. -/
theorem wellLinked_of_passive_reducts {P : Proc}
    (hheads : ∀ (E : Ctx) (R : Proc) (a : Name),
      Congr P (E.fill R) → SharedHead R a →
      ∃ (E' : Ctx) (S : Proc), Congr P (E'.fill S) ∧ SharedRedexContains R S a)
    (hstep : ∀ Q, Reduces P Q → Passive Q) : WellLinked P := by
  have hclass : ∀ Q, Relation.ReflTransGen Reduces P Q → Q = P ∨ Passive Q := by
    intro Q hreach
    induction hreach with
    | refl => exact Or.inl rfl
    | tail hreach hlast ih =>
      rcases ih with rfl | hp
      · exact Or.inr (hstep _ hlast)
      · exact False.elim (passive_no_reduction hlast hp)
  intro Q hreach E R a hc hs
  rcases hclass Q hreach with rfl | hp
  · exact hheads E R a hc hs
  · exact False.elim (passive_no_shared hp E R a hc hs)

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

theorem initial_almostPassive : AlmostPassive initial := by
  simp [initial, requester, accepter, receiver, AlmostPassive, Passive]

theorem initial_shared_count : sharedCount initial = 2 := rfl

theorem initial_reduct_passive {Q : Proc} (h : Reduces initial Q) : Passive Q :=
  (almostPassive_reduction h initial_almostPassive (by rw [initial_shared_count])).1

theorem initial_free_shared_count : freeSharedCount initial 0 = sharedCount initial := rfl

theorem initial_shared_parameters : SharedParameters initial := by
  simp [initial, requester, accepter, SharedParameters]

theorem initial_exposed_subject (E : Ctx) (R : Proc) (a : Name)
    (hc : Congr initial (E.fill R)) (hs : SharedHead R a) : a = 0 :=
  sharedHead_subject_of_full_count initial 0 initial_free_shared_count E R a hc hs

theorem initial_exposed_parameters (E : Ctx) (R : Proc)
    (hc : Congr initial (E.fill R)) : SharedParameters R :=
  sharedParameters_of_fill E R ((sharedParameters_congr hc).mp initial_shared_parameters)

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

mutual
/-- Renaming is independent of the fuel once it exceeds the syntax size. -/
theorem renameFuel_stable (P : Proc) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.renameFuel m ν χ ξ P = Proc.renameFuel n ν χ ξ P := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | accept a k ss P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | send c es P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | recv c xs P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | deleg c ss P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | srecv c ss P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | sel c l P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | resN a P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | resS ss P =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | branch c bs =>
        simp only [Proc.renameFuel]
        congr 1
        apply List.map_congr_left
        rintro ⟨l, Q⟩ hx
        have hsize := List.sizeOf_lt_of_mem hx
        simp only [Prod.mk.sizeOf_spec] at hsize
        congr 1
        exact renameFuel_stable Q m n ν χ ξ
          (by have h := List.sizeOf_lt_of_mem hx; simp_all; omega)
          (by have h := List.sizeOf_lt_of_mem hx; simp_all; omega)
      | ite e P Q =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega),
          renameFuel_stable Q m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | par P Q =>
        simp only [Proc.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega),
          renameFuel_stable Q m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
      | defn D P =>
        simp only [Proc.renameFuel]
        congr 1
        · apply List.map_congr_left
          intro d hd
          exact renameDeclFuel_stable d m n ν χ ξ
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)
        · exact renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)
      | nil | call _ _ _ | queue _ _ => rfl
termination_by m

theorem renameDeclFuel_stable (d : Decl) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.renameFuel m ν χ ξ d = Decl.renameFuel n ν χ ξ d := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.renameFuel]
        rw [renameFuel_stable P m n ν χ ξ (by simp_all; omega) (by simp_all; omega)]
termination_by m
end


theorem val_rename_comp (v : Val) (ν₁ ν₂ : Name → Name) :
    (v.rename ν₁).rename ν₂ = v.rename (ν₂ ∘ ν₁) := by
  cases v <;> rfl

theorem expr_rename_comp (e : Expr) (ν₁ ν₂ : Name → Name) :
    (e.rename ν₁).rename ν₂ = e.rename (ν₂ ∘ ν₁) := by
  induction e <;> simp_all [Expr.rename, val_rename_comp]

theorem msg_rename_comp (h : Msg) (ν₁ ν₂ : Name → Name) (χ₁ χ₂ : Chan → Chan) :
    (h.rename ν₁ χ₁).rename ν₂ χ₂ = h.rename (ν₂ ∘ ν₁) (χ₂ ∘ χ₁) := by
  cases h <;> simp [Msg.rename, List.map_map, Function.comp_def, val_rename_comp]

theorem renameFuel_comp_all (n : Nat)
    (ν₁ ν₂ : Name → Name) (χ₁ χ₂ : Chan → Chan) (ξ₁ ξ₂ : PVar → PVar) :
    (∀ P, Proc.renameFuel n ν₂ χ₂ ξ₂ (Proc.renameFuel n ν₁ χ₁ ξ₁ P) =
      Proc.renameFuel n (ν₂ ∘ ν₁) (χ₂ ∘ χ₁) (ξ₂ ∘ ξ₁) P) ∧
    (∀ d, Decl.renameFuel n ν₂ χ₂ ξ₂ (Decl.renameFuel n ν₁ χ₁ ξ₁ d) =
      Decl.renameFuel n (ν₂ ∘ ν₁) (χ₂ ∘ χ₁) (ξ₂ ∘ ξ₁) d) := by
  induction n with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rcases ih with ⟨ihP, ihD⟩
    constructor
    · intro P
      cases P <;> simp [Proc.renameFuel, List.map_map, Function.comp_def,
        expr_rename_comp, msg_rename_comp, ihP, ihD]
    · intro d
      cases d <;> simp [Decl.renameFuel, List.map_map, Function.comp_def, ihP]

theorem rename_comp (P : Proc)
    (ν₁ ν₂ : Name → Name) (χ₁ χ₂ : Chan → Chan) (ξ₁ ξ₂ : PVar → PVar) :
    (P.rename ν₁ χ₁ ξ₁).rename ν₂ χ₂ ξ₂ =
      P.rename (ν₂ ∘ ν₁) (χ₂ ∘ χ₁) (ξ₂ ∘ ξ₁) := by
  let n := max (sizeOf P) (sizeOf (P.rename ν₁ χ₁ ξ₁))
  have h₁ : sizeOf P ≤ n := le_max_left _ _
  have h₂ : sizeOf (P.rename ν₁ χ₁ ξ₁) ≤ n := le_max_right _ _
  calc
    (P.rename ν₁ χ₁ ξ₁).rename ν₂ χ₂ ξ₂ =
        Proc.renameFuel n ν₂ χ₂ ξ₂ (P.rename ν₁ χ₁ ξ₁) :=
      renameFuel_stable _ _ _ _ _ _ le_rfl h₂
    _ = Proc.renameFuel n ν₂ χ₂ ξ₂ (Proc.renameFuel n ν₁ χ₁ ξ₁ P) := by
      rw [renameFuel_stable P n (sizeOf P) ν₁ χ₁ ξ₁ h₁ le_rfl]
      rfl
    _ = Proc.renameFuel n (ν₂ ∘ ν₁) (χ₂ ∘ χ₁) (ξ₂ ∘ ξ₁) P :=
      (renameFuel_comp_all n ν₁ ν₂ χ₁ χ₂ ξ₁ ξ₂).1 P
    _ = P.rename (ν₂ ∘ ν₁) (χ₂ ∘ χ₁) (ξ₂ ∘ ξ₁) :=
      renameFuel_stable _ _ _ _ _ _ h₁ le_rfl

theorem val_rename_id (v : Val) : v.rename id = v := by cases v <;> rfl

theorem expr_rename_id (e : Expr) : e.rename id = e := by
  induction e <;> simp_all [Expr.rename, val_rename_id]

theorem msg_rename_id (h : Msg) : h.rename id id = h := by
  cases h <;> simp [Msg.rename, show Val.rename id = id from funext val_rename_id]

theorem renameFuel_id_all (n : Nat) :
    (∀ P, Proc.renameFuel n id id id P = P) ∧
    (∀ d, Decl.renameFuel n id id id d = d) := by
  induction n with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
    rcases ih with ⟨ihP, ihD⟩
    constructor
    · intro P
      cases P <;> simp [Proc.renameFuel, ihP,
        show Expr.rename id = id from funext expr_rename_id,
        show Msg.rename id id = id from funext msg_rename_id,
        show Decl.renameFuel n id id id = id from funext ihD]
    · intro d
      cases d <;> simp [Decl.renameFuel, ihP]

@[simp] theorem rename_id (P : Proc) : P.rename id id id = P :=
  (renameFuel_id_all (sizeOf P)).1 P

/-- Canonical full renaming of a declaration, matching the process traversal. -/
noncomputable def renameDecl (d : Decl) (ν : Name → Name)
    (χ : Chan → Chan) (ξ : PVar → PVar) : Decl :=
  Decl.renameFuel (sizeOf d) ν χ ξ d

@[simp] theorem rename_request (a : Name) (k : Nat) (ss : List Chan) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.request a k ss P).rename ν χ ξ = .request (ν a) k (ss.map χ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.request a k ss P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_accept (a : Name) (k : Nat) (ss : List Chan) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.accept a k ss P).rename ν χ ξ = .accept (ν a) k (ss.map χ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.accept a k ss P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_send (c : Chan) (es : List Expr) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.send c es P).rename ν χ ξ = .send (χ c) (es.map (Expr.rename ν)) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.send c es P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_recv (c : Chan) (xs : List Name) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.recv c xs P).rename ν χ ξ = .recv (χ c) (xs.map ν) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.recv c xs P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_deleg (c : Chan) (ss : List Chan) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.deleg c ss P).rename ν χ ξ = .deleg (χ c) (ss.map χ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.deleg c ss P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_srecv (c : Chan) (ss : List Chan) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.srecv c ss P).rename ν χ ξ = .srecv (χ c) (ss.map χ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.srecv c ss P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_sel (c : Chan) (l : Label) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.sel c l P).rename ν χ ξ = .sel (χ c) l (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.sel c l P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_resN (a : Name) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.resN a P).rename ν χ ξ = .resN (ν a) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.resN a P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_resS (ss : List Chan) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.resS ss P).rename ν χ ξ = .resS (ss.map χ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.resS ss P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_ite (e : Expr) (P Q : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.ite e P Q).rename ν χ ξ = .ite (e.rename ν) (P.rename ν χ ξ) (Q.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.ite e P Q) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    · exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl
    · exact renameFuel_stable Q f (sizeOf Q) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_par (P Q : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.par P Q).rename ν χ ξ = .par (P.rename ν χ ξ) (Q.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.par P Q) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    · exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl
    · exact renameFuel_stable Q f (sizeOf Q) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_nil 
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.nil ).rename ν χ ξ = .nil := by
  cases hf : sizeOf (Proc.nil ) with
  | zero => simp at hf
  | succ f => rw [Proc.rename, hf, Proc.renameFuel]

@[simp] theorem rename_call (X : PVar) (es : List Expr) (ss : List Chan)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.call X es ss).rename ν χ ξ = .call (ξ X) (es.map (Expr.rename ν)) (ss.map χ) := by
  cases hf : sizeOf (Proc.call X es ss) with
  | zero => simp at hf
  | succ f => rw [Proc.rename, hf, Proc.renameFuel]

@[simp] theorem rename_queue (c : Chan) (h : List Msg)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.queue c h).rename ν χ ξ = .queue (χ c) (h.map (Msg.rename ν χ)) := by
  cases hf : sizeOf (Proc.queue c h) with
  | zero => simp at hf
  | succ f => rw [Proc.rename, hf, Proc.renameFuel]

@[simp] theorem rename_branch (c : Chan) (bs : List (Label × Proc))
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.branch c bs).rename ν χ ξ =
      .branch (χ c) (bs.map fun x => (x.1,x.2.rename ν χ ξ)) := by
  cases hf : sizeOf (Proc.branch c bs) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    apply List.map_congr_left
    rintro ⟨l, P⟩ hp
    have hs := List.sizeOf_lt_of_mem hp
    simp only [Prod.mk.sizeOf_spec] at hs
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem rename_defn (D : List Decl) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.defn D P).rename ν χ ξ =
      .defn (D.map fun d => renameDecl d ν χ ξ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Proc.defn D P) with
  | zero => simp at hf
  | succ f =>
    rw [Proc.rename, hf, Proc.renameFuel]
    congr 1
    · apply List.map_congr_left
      intro d hd
      have hs := List.sizeOf_lt_of_mem hd
      exact renameDeclFuel_stable d f (sizeOf d) ν χ ξ (by simp at hf; omega) le_rfl
    · exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem renameDecl_mk (X : PVar) (xs : List Name) (ss : List Chan) (P : Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    renameDecl (.mk X xs ss P) ν χ ξ =
      .mk (ξ X) (xs.map ν) (ss.map χ) (P.rename ν χ ξ) := by
  cases hf : sizeOf (Decl.mk X xs ss P) with
  | zero => simp at hf
  | succ f =>
    rw [renameDecl, hf, Decl.renameFuel]
    congr 1
    exact renameFuel_stable P f (sizeOf P) ν χ ξ (by simp at hf; omega) le_rfl

@[simp] theorem renameDecl_name (d : Decl)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (renameDecl d ν χ ξ).name = ξ d.name := by
  cases d
  simp [Decl.name]

theorem renameFuel_eq_rename (P : Proc) (fuel : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hf : sizeOf P ≤ fuel) : Proc.renameFuel fuel ν χ ξ P = P.rename ν χ ξ :=
  renameFuel_stable P fuel (sizeOf P) ν χ ξ hf le_rfl

@[simp] theorem rename_equiv_symm (P : Proc)
    (ν : Name ≃ Name) (χ : Chan ≃ Chan) (ξ : PVar ≃ PVar) :
    (P.rename ν χ ξ).rename ν.symm χ.symm ξ.symm = P := by
  rw [rename_comp]
  simp only [Function.comp_def, Equiv.symm_apply_apply]
  exact rename_id P

@[simp] theorem rename_symm_equiv (P : Proc)
    (ν : Name ≃ Name) (χ : Chan ≃ Chan) (ξ : PVar ≃ PVar) :
    (P.rename ν.symm χ.symm ξ.symm).rename ν χ ξ = P := by
  rw [rename_comp]
  simp only [Function.comp_def, Equiv.apply_symm_apply]
  exact rename_id P

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

/-- Equivariance of alpha-conversion, with the three free-support equations isolated. -/
theorem alpha_rename_of_support
    (ν : Name ≃ Name) (χ : Chan ≃ Chan) (ξ : PVar ≃ PVar)
    (hN : ∀ P : Proc, (P.rename ν χ ξ).freeNames = P.freeNames.image ν)
    (hC : ∀ P : Proc, (P.rename ν χ ξ).freeChans = P.freeChans.image χ)
    (hX : ∀ P : Proc, (P.rename ν χ ξ).freePVars = P.freePVars.image ξ)
    {P Q : Proc} (h : Alpha P Q) :
    Alpha (P.rename ν χ ξ) (Q.rename ν χ ξ) := by
  obtain ⟨ρ, κ, η, hρ, hκ, hη, hρfix, hκfix, hηfix, rfl⟩ := h
  let ρ' : Name → Name := fun a => ν (ρ (ν.symm a))
  let κ' : Chan → Chan := fun c => χ (κ (χ.symm c))
  let η' : PVar → PVar := fun X => ξ (η (ξ.symm X))
  refine ⟨ρ', κ', η', ν.bijective.comp (hρ.comp ν.symm.bijective),
    χ.bijective.comp (hκ.comp χ.symm.bijective),
    ξ.bijective.comp (hη.comp ξ.symm.bijective), ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hN P] at ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
    simpa [ρ'] using congrArg ν (hρfix b hb)
  · intro c hc
    rw [hC P] at hc
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hc
    simpa [κ'] using congrArg χ (hκfix d hd)
  · intro X hXmem
    rw [hX P] at hXmem
    obtain ⟨Y, hY, rfl⟩ := Finset.mem_image.mp hXmem
    simpa [η'] using congrArg ξ (hηfix Y hY)
  · simp only [rename_comp]
    congr 1 <;> funext a <;> simp [ρ', κ', η']

@[simp] theorem rename_parList (ps : List Proc)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.parList ps).rename ν χ ξ = Proc.parList (ps.map fun P => P.rename ν χ ξ) := by
  induction ps with
  | nil => simp [Proc.parList]
  | cons P ps ih =>
    simpa only [Proc.parList, List.foldr_cons, List.map_cons, rename_par] using
      (congrArg (Proc.par (P.rename ν χ ξ)) ih)

@[simp] theorem rename_queues (ss : List Chan)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar) :
    (Proc.queues ss).rename ν χ ξ = Proc.queues (ss.map χ) := by
  simp [Proc.queues, List.map_map, Function.comp_def]

/-- Structural congruence commutes with bijective identifier renaming. The support equations
are isolated so their independently checked syntax traversals can be supplied directly. -/
theorem congr_rename_of_support
    (ν : Name ≃ Name) (χ : Chan ≃ Chan) (ξ : PVar ≃ PVar)
    (hN : ∀ P : Proc, (P.rename ν χ ξ).freeNames = P.freeNames.image ν)
    (hC : ∀ P : Proc, (P.rename ν χ ξ).freeChans = P.freeChans.image χ)
    (hX : ∀ P : Proc, (P.rename ν χ ξ).freePVars = P.freePVars.image ξ)
    (hDN : ∀ d : Decl, (renameDecl d ν χ ξ).freeNames = d.freeNames.image ν)
    (hDC : ∀ d : Decl, (renameDecl d ν χ ξ).freeChans = d.freeChans.image χ)
    {P Q : Proc} (h : Congr P Q) : Congr (P.rename ν χ ξ) (Q.rename ν χ ξ) := by
  induction h with
  | alpha P Q h => exact .alpha _ _ (alpha_rename_of_support ν χ ξ hN hC hX h)
  | refl P => exact .refl _
  | symm P Q h ih => exact .symm _ _ ih
  | trans P Q R h h' ih ih' => exact .trans _ _ _ ih ih'
  | parNil P => simpa using Congr.parNil (P.rename ν χ ξ)
  | parComm P Q => simpa using Congr.parComm (P.rename ν χ ξ) (Q.rename ν χ ξ)
  | parAssoc P Q R =>
    simpa using Congr.parAssoc (P.rename ν χ ξ) (Q.rename ν χ ξ) (R.rename ν χ ξ)
  | scopeN a P Q hfresh =>
    simp only [rename_par, rename_resN]
    apply Congr.scopeN
    rw [hN Q]
    intro hm
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hm
    exact hfresh (ν.injective hba ▸ hb)
  | scopeS ss P Q hfresh =>
    simp only [rename_par, rename_resS]
    apply Congr.scopeS
    intro c hc hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    rw [hC Q] at hm
    obtain ⟨d, hd, hdb⟩ := Finset.mem_image.mp hm
    exact hfresh b hb (χ.injective hdb ▸ hd)
  | resNN a b P => simpa using Congr.resNN (ν a) (ν b) (P.rename ν χ ξ)
  | resSS ss ts P => simpa using Congr.resSS (ss.map χ) (ts.map χ) (P.rename ν χ ξ)
  | resNS a ss P => simpa using Congr.resNS (ν a) (ss.map χ) (P.rename ν χ ξ)
  | resNilN a => simpa using Congr.resNilN (ν a)
  | resNilS ss => simpa using Congr.resNilS (ss.map χ)
  | emptyQueues ss => simpa using Congr.emptyQueues (ss.map χ)
  | defNil D => simpa using Congr.defNil (D.map fun d => renameDecl d ν χ ξ)
  | defResN D a P hfresh =>
    simp only [rename_defn, rename_resN]
    apply Congr.defResN
    intro d hd hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    rw [hDN e] at hm
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hm
    exact hfresh e he (ν.injective hba ▸ hb)
  | defResS D ss P hfresh =>
    simp only [rename_defn, rename_resS]
    apply Congr.defResS
    intro d hd c hc hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
    rw [hDC e] at hm
    obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp hm
    exact hfresh e he b hb (χ.injective hab ▸ ha)
  | defPar D P Q hfresh =>
    simp only [rename_par, rename_defn]
    apply Congr.defPar
    intro d hd X hXm hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hd
    cases e with
    | mk Y xs ss B =>
      simp only [renameDecl_mk, Finset.mem_singleton] at hXm
      subst X
      rw [hX Q] at hm
      obtain ⟨Z, hZ, hZY⟩ := Finset.mem_image.mp hm
      exact hfresh (.mk Y xs ss B) he Y (by simp) (ξ.injective hZY ▸ hZ)
  | defMerge D D' P hdisj =>
    simp only [rename_defn, List.map_append]
    apply Congr.defMerge
    change (D.map Decl.name).toFinset ∩ (D'.map Decl.name).toFinset = ∅ at hdisj
    change ((D.map fun d => renameDecl d ν χ ξ).map Decl.name).toFinset ∩
      ((D'.map fun d => renameDecl d ν χ ξ).map Decl.name).toFinset = ∅
    have heq (ds : List Decl) :
        ((ds.map fun d => renameDecl d ν χ ξ).map Decl.name).toFinset =
          (ds.map Decl.name).toFinset.image ξ := by
      ext y
      simp only [List.map_map, Function.comp_def, renameDecl_name, List.mem_toFinset,
        List.mem_map, Finset.mem_image]
      constructor
      · rintro ⟨d, hd, hy⟩
        exact ⟨d.name, ⟨d, hd, rfl⟩, hy⟩
      · rintro ⟨x, ⟨d, hd, rfl⟩, hy⟩
        exact ⟨d, hd, hy⟩
    rw [heq, heq, ← Finset.image_inter _ _ ξ.injective, hdisj]
    simp
  | request a n ss P Q h ih =>
    simpa using Congr.request (ν a) n (ss.map χ) _ _ ih
  | accept a p ss P Q h ih =>
    simpa using Congr.accept (ν a) p (ss.map χ) _ _ ih
  | send c es P Q h ih => simpa using Congr.send (χ c) (es.map (Expr.rename ν)) _ _ ih
  | recv c xs P Q h ih => simpa using Congr.recv (χ c) (xs.map ν) _ _ ih
  | deleg c ts P Q h ih => simpa using Congr.deleg (χ c) (ts.map χ) _ _ ih
  | srecv c ts P Q h ih => simpa using Congr.srecv (χ c) (ts.map χ) _ _ ih
  | sel c l P Q h ih => simpa using Congr.sel (χ c) l _ _ ih
  | branch c bs bs' hlabels h ih =>
    simp only [rename_branch]
    apply Congr.branch
    · simpa [List.map_map, Function.comp_def] using hlabels
    · intro x hx y hy hxy
      obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hx
      obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hy
      exact ih u hu v hv hxy
  | iteLeft e P P' Q h ih => simpa using Congr.iteLeft (e.rename ν) _ _ _ ih
  | iteRight e P Q Q' h ih => simpa using Congr.iteRight (e.rename ν) _ _ _ ih
  | parLeft P P' Q h ih => simpa using Congr.parLeft _ _ (Q.rename ν χ ξ) ih
  | parRight P Q Q' h ih => simpa using Congr.parRight (P.rename ν χ ξ) _ _ ih
  | resN a P Q h ih => simpa using Congr.resN (ν a) _ _ ih
  | resS ss P Q h ih => simpa using Congr.resS (ss.map χ) _ _ ih
  | defn D P Q h ih =>
    simpa using Congr.defn (D.map fun d => renameDecl d ν χ ξ) _ _ ih
  | defnBodies n X xs ss Ps Qs P h ih =>
    simpa [List.map_ofFn, Function.comp_def] using Congr.defnBodies n (fun i => ξ (X i))
      (fun i => (xs i).map ν) (fun i => (ss i).map χ)
      (fun i => (Ps i).rename ν χ ξ) (fun i => (Qs i).rename ν χ ξ)
      (P.rename ν χ ξ) ih

end MPSTAsync.Progress.Counterexample






set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

theorem fold_union_congr {α : Type} (xs : List α) (f g : α → Finset Nat)
    (h : ∀ x ∈ xs, f x = g x) (z : Finset Nat) :
    xs.foldl (fun a x ↦ a ∪ f x) z = xs.foldl (fun a x ↦ a ∪ g x) z := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [h x (by simp)]
    exact ih (fun y hy ↦ h y (by simp [hy])) _

mutual
theorem freeNamesFuel_stable (P : Proc) (m n : Nat)
    (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.freeNamesFuel m P = Proc.freeNamesFuel n P := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | accept a k ss P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | send c es P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | recv c xs P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | deleg c ss P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | srecv c ss P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | sel c l P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | resN a P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | resS ss P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | branch c bs =>
        simp only [Proc.freeNamesFuel]
        apply fold_union_congr
        intro x hx
        have hsize := List.sizeOf_lt_of_mem hx
        rcases x with ⟨l, Q⟩
        simp only [Prod.mk.sizeOf_spec] at hsize
        exact freeNamesFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)
      | ite e P Q =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega),
          freeNamesFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)]
      | par P Q =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega),
          freeNamesFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)]
      | defn D P =>
        simp only [Proc.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
        have heq : D.foldl (fun a d ↦ a ∪ Decl.freeNamesFuel m d) ∅ =
            D.foldl (fun a d ↦ a ∪ Decl.freeNamesFuel n d) ∅ := by
          apply fold_union_congr
          intro d hd
          have hsize := List.sizeOf_lt_of_mem hd
          exact freeNamesDeclFuel_stable d m n (by simp_all; omega) (by simp_all; omega)
        rw [heq]
      | nil | call _ _ _ | queue _ _ => rfl
termination_by m
decreasing_by all_goals omega

theorem freeNamesDeclFuel_stable (d : Decl) (m n : Nat)
    (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.freeNamesFuel m d = Decl.freeNamesFuel n d := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.freeNamesFuel]
        rw [freeNamesFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
termination_by m
end

mutual
theorem freeChansFuel_stable (P : Proc) (m n : Nat)
    (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.freeChansFuel m P = Proc.freeChansFuel n P := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | accept a k ss P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | send c es P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | recv c xs P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | deleg c ss P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | srecv c ss P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | sel c l P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | resN a P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | resS ss P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | branch c bs =>
        simp only [Proc.freeChansFuel]
        congr 1
        apply fold_union_congr
        intro x hx
        have hsize := List.sizeOf_lt_of_mem hx
        rcases x with ⟨l, Q⟩
        simp only [Prod.mk.sizeOf_spec] at hsize
        exact freeChansFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)
      | ite e P Q =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega),
          freeChansFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)]
      | par P Q =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega),
          freeChansFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)]
      | defn D P =>
        simp only [Proc.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
        have heq : D.foldl (fun a d ↦ a ∪ Decl.freeChansFuel m d) ∅ =
            D.foldl (fun a d ↦ a ∪ Decl.freeChansFuel n d) ∅ := by
          apply fold_union_congr
          intro d hd
          have hsize := List.sizeOf_lt_of_mem hd
          exact freeChansDeclFuel_stable d m n (by simp_all; omega) (by simp_all; omega)
        rw [heq]
      | nil | call _ _ _ | queue _ _ => rfl
termination_by m
decreasing_by all_goals omega

theorem freeChansDeclFuel_stable (d : Decl) (m n : Nat)
    (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.freeChansFuel m d = Decl.freeChansFuel n d := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.freeChansFuel]
        rw [freeChansFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
termination_by m
end

mutual
theorem freePVarsFuel_stable (P : Proc) (m n : Nat)
    (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.freePVarsFuel m P = Proc.freePVarsFuel n P := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | accept a k ss P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | send c es P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | recv c xs P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | deleg c ss P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | srecv c ss P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | sel c l P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | resN a P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | resS ss P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
      | branch c bs =>
        simp only [Proc.freePVarsFuel]
        apply fold_union_congr
        intro x hx
        have hsize := List.sizeOf_lt_of_mem hx
        rcases x with ⟨l, Q⟩
        simp only [Prod.mk.sizeOf_spec] at hsize
        exact freePVarsFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)
      | ite e P Q =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega),
          freePVarsFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)]
      | par P Q =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega),
          freePVarsFuel_stable Q m n (by simp_all; omega) (by simp_all; omega)]
      | defn D P =>
        simp only [Proc.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
        have heq : D.foldl (fun a d ↦ a ∪ Decl.freePVarsFuel m d) ∅ =
            D.foldl (fun a d ↦ a ∪ Decl.freePVarsFuel n d) ∅ := by
          apply fold_union_congr
          intro d hd
          have hsize := List.sizeOf_lt_of_mem hd
          exact freePVarsDeclFuel_stable d m n (by simp_all; omega) (by simp_all; omega)
        rw [heq]
      | nil | call _ _ _ | queue _ _ => rfl
termination_by m
decreasing_by all_goals omega

theorem freePVarsDeclFuel_stable (d : Decl) (m n : Nat)
    (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.freePVarsFuel m d = Decl.freePVarsFuel n d := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.freePVarsFuel]
        rw [freePVarsFuel_stable P m n (by simp_all; omega) (by simp_all; omega)]
termination_by m
end

theorem list_toFinset_map (xs : List Nat) (f : Nat → Nat) :
    (xs.map f).toFinset = xs.toFinset.image f := by
  ext x
  simp

theorem fold_support_image {α β : Type} (xs : List α) (r : α → β)
    (f : α → Finset Nat) (g : β → Finset Nat) (ν : Nat → Nat)
    (h : ∀ x ∈ xs, g (r x) = (f x).image ν) (z : Finset Nat) :
    (xs.map r).foldl (fun a x ↦ a ∪ g x) (z.image ν) =
      (xs.foldl (fun a x ↦ a ∪ f x) z).image ν := by
  induction xs generalizing z with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [h x (by simp), ← Finset.image_union]
    exact ih (fun y hy ↦ h y (by simp [hy])) _

theorem val_names_rename (v : Val) (ν : Name → Name) :
    (v.rename ν).names = v.names.image ν := by
  cases v <;> simp [Val.rename, Val.names]

theorem expr_names_rename (e : Expr) (ν : Name → Name) :
    (e.rename ν).names = e.names.image ν := by
  induction e <;> simp_all [Expr.rename, Expr.names, val_names_rename, Finset.image_union]

theorem msg_names_rename (v : Msg) (ν : Name → Name) (χ : Chan → Chan) :
    (v.rename ν χ).names = v.names.image ν := by
  cases v with
  | label l => simp [Msg.rename, Msg.names]
  | chans cs => simp [Msg.rename, Msg.names]
  | vals vs =>
    simpa [Msg.rename, Msg.names] using
      fold_support_image vs (Val.rename ν) Val.names Val.names ν
        (fun x _ ↦ val_names_rename x ν) ∅

mutual
theorem freeNamesFuel_rename (P : Proc) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hν : Function.Injective ν) (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.freeNamesFuel n (Proc.renameFuel m ν χ ξ P) =
      (Proc.freeNamesFuel n P).image ν := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | accept a k ss P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | recv c xs P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | deleg c ss P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | srecv c ss P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | sel c l P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | resN a P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | resS ss P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        try simp [list_toFinset_map, Finset.image_sdiff _ _ hν, Finset.image_erase hν]
      | send c es P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        exact fold_support_image es (Expr.rename ν) Expr.names Expr.names ν
          (fun x _ ↦ expr_names_rename x ν) _
      | branch c bs =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        simpa using fold_support_image bs
          (fun x ↦ (x.1, Proc.renameFuel m ν χ ξ x.2))
          (fun x ↦ Proc.freeNamesFuel n x.2) (fun x ↦ Proc.freeNamesFuel n x.2) ν
          (fun x hx ↦ freeNamesFuel_rename x.2 m n ν χ ξ hν
            (by have h := List.sizeOf_lt_of_mem hx; cases x; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hx; cases x; simp_all; omega)) ∅
      | ite e P Q =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega),
          freeNamesFuel_rename Q m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        simp [expr_names_rename, Finset.image_union]
      | par P Q =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega),
          freeNamesFuel_rename Q m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        simp [expr_names_rename, Finset.image_union]
      | nil => simp [Proc.renameFuel, Proc.freeNamesFuel]
      | call X es ss =>
        simpa [Proc.renameFuel, Proc.freeNamesFuel] using
          fold_support_image es (Expr.rename ν) Expr.names Expr.names ν
            (fun x _ ↦ expr_names_rename x ν) ∅
      | queue c h =>
        simpa [Proc.renameFuel, Proc.freeNamesFuel] using
          fold_support_image h (Msg.rename ν χ) Msg.names Msg.names ν
            (fun x _ ↦ msg_names_rename x ν χ) ∅
      | defn D P =>
        simp only [Proc.renameFuel, Proc.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        have hd := fold_support_image D (Decl.renameFuel m ν χ ξ)
          (Decl.freeNamesFuel n) (Decl.freeNamesFuel n) ν
          (fun d hd ↦ freeNamesDeclFuel_rename d m n ν χ ξ hν
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)) ∅
        simpa [Finset.image_union] using congrArg (fun s ↦ (Proc.freeNamesFuel n P).image ν ∪ s) hd
termination_by m

theorem freeNamesDeclFuel_rename (d : Decl) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hν : Function.Injective ν) (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.freeNamesFuel n (Decl.renameFuel m ν χ ξ d) =
      (Decl.freeNamesFuel n d).image ν := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.renameFuel, Decl.freeNamesFuel]
        rw [freeNamesFuel_rename P m n ν χ ξ hν (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_sdiff _ _ hν]
termination_by m
end

theorem freeNames_rename (P : Proc) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (hν : Function.Injective ν) :
    (P.rename ν χ ξ).freeNames = P.freeNames.image ν := by
  let Q := P.rename ν χ ξ
  let n := max (sizeOf P) (sizeOf Q)
  rw [Proc.freeNames, ← freeNamesFuel_stable Q n (sizeOf Q) (Nat.le_max_right _ _) le_rfl]
  change Proc.freeNamesFuel n (Proc.renameFuel (sizeOf P) ν χ ξ P) = P.freeNames.image ν
  rw [freeNamesFuel_rename P (sizeOf P) n ν χ ξ hν le_rfl (Nat.le_max_left _ _)]
  rw [freeNamesFuel_stable P n (sizeOf P) (Nat.le_max_left _ _) le_rfl]
  rfl

theorem freeNames_renameDecl (d : Decl) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (hν : Function.Injective ν) :
    (renameDecl d ν χ ξ).freeNames = d.freeNames.image ν := by
  let e := renameDecl d ν χ ξ
  let n := max (sizeOf d) (sizeOf e)
  rw [Decl.freeNames, ← freeNamesDeclFuel_stable e n (sizeOf e) (Nat.le_max_right _ _) le_rfl]
  change Decl.freeNamesFuel n (Decl.renameFuel (sizeOf d) ν χ ξ d) = d.freeNames.image ν
  rw [freeNamesDeclFuel_rename d (sizeOf d) n ν χ ξ hν le_rfl (Nat.le_max_left _ _)]
  rw [freeNamesDeclFuel_stable d n (sizeOf d) (Nat.le_max_left _ _) le_rfl]
  rfl

theorem fold_decl_names (D : List Decl) (z : Finset PVar) :
    D.foldl (fun a d ↦ match d with | .mk X _ _ _ => insert X a) z =
      (D.map Decl.name).toFinset ∪ z := by
  induction D generalizing z with
  | nil => simp
  | cons d ds ih =>
    cases d
    simp [ih, Decl.name, Finset.union_assoc, Finset.union_left_comm, Finset.union_comm]

theorem renameDeclFuel_name (d : Decl) (m : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hm : sizeOf d ≤ m) :
    (Decl.renameFuel m ν χ ξ d).name = ξ d.name := by
  cases d
  cases m <;> simp_all [Decl.renameFuel, Decl.name]

mutual
theorem freePVarsFuel_rename (P : Proc) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hξ : Function.Injective ξ) (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.freePVarsFuel n (Proc.renameFuel m ν χ ξ P) =
      (Proc.freePVarsFuel n P).image ξ := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P | accept a k ss P | send c es P | recv c xs P
      | deleg c ss P | srecv c ss P | sel c l P | resN a P | resS ss P =>
        simp only [Proc.renameFuel, Proc.freePVarsFuel]
        exact freePVarsFuel_rename P m n ν χ ξ hξ (by simp_all; omega) (by simp_all; omega)
      | branch c bs =>
        simp only [Proc.renameFuel, Proc.freePVarsFuel]
        simpa using fold_support_image bs
          (fun x ↦ (x.1, Proc.renameFuel m ν χ ξ x.2))
          (fun x ↦ Proc.freePVarsFuel n x.2) (fun x ↦ Proc.freePVarsFuel n x.2) ξ
          (fun x hx ↦ freePVarsFuel_rename x.2 m n ν χ ξ hξ
            (by have h := List.sizeOf_lt_of_mem hx; cases x; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hx; cases x; simp_all; omega)) ∅
      | ite e P Q | par P Q =>
        simp only [Proc.renameFuel, Proc.freePVarsFuel]
        rw [freePVarsFuel_rename P m n ν χ ξ hξ (by simp_all; omega) (by simp_all; omega),
          freePVarsFuel_rename Q m n ν χ ξ hξ (by simp_all; omega) (by simp_all; omega)]
        simp [Finset.image_union]
      | nil | call _ _ _ | queue _ _ => simp [Proc.renameFuel, Proc.freePVarsFuel]
      | defn D P =>
        simp only [Proc.renameFuel, Proc.freePVarsFuel]
        rw [freePVarsFuel_rename P m n ν χ ξ hξ (by simp_all; omega) (by simp_all; omega)]
        have hd := fold_support_image D (Decl.renameFuel m ν χ ξ)
          (Decl.freePVarsFuel n) (Decl.freePVarsFuel n) ξ
          (fun d hd ↦ freePVarsDeclFuel_rename d m n ν χ ξ hξ
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)) ∅
        simp only [Finset.image_empty] at hd
        rw [hd]
        erw [fold_decl_names, fold_decl_names]
        have hb : ((D.map (Decl.renameFuel m ν χ ξ)).map Decl.name) = (D.map Decl.name).map ξ := by
          simp only [List.map_map]
          apply List.map_congr_left
          intro d hd
          exact renameDeclFuel_name d m ν χ ξ (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)
        rw [hb, list_toFinset_map]
        simp [Finset.image_sdiff _ _ hξ, Finset.image_union]
termination_by m

theorem freePVarsDeclFuel_rename (d : Decl) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hξ : Function.Injective ξ) (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.freePVarsFuel n (Decl.renameFuel m ν χ ξ d) =
      (Decl.freePVarsFuel n d).image ξ := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.renameFuel, Decl.freePVarsFuel]
        exact freePVarsFuel_rename P m n ν χ ξ hξ (by simp_all; omega) (by simp_all; omega)
termination_by m
end

theorem freePVars_rename (P : Proc) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (hξ : Function.Injective ξ) :
    (P.rename ν χ ξ).freePVars = P.freePVars.image ξ := by
  let Q := P.rename ν χ ξ
  let n := max (sizeOf P) (sizeOf Q)
  rw [Proc.freePVars, ← freePVarsFuel_stable Q n (sizeOf Q) (Nat.le_max_right _ _) le_rfl]
  change Proc.freePVarsFuel n (Proc.renameFuel (sizeOf P) ν χ ξ P) = P.freePVars.image ξ
  rw [freePVarsFuel_rename P (sizeOf P) n ν χ ξ hξ le_rfl (Nat.le_max_left _ _)]
  rw [freePVarsFuel_stable P n (sizeOf P) (Nat.le_max_left _ _) le_rfl]
  rfl

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

theorem msg_chans_rename (v : Msg) (ν : Name → Name) (χ : Chan → Chan) :
    (v.rename ν χ).freeChans = v.freeChans.image χ := by
  cases v <;> simp [Msg.rename, Msg.freeChans, list_toFinset_map]

mutual
theorem freeChansFuel_rename (P : Proc) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hχ : Function.Injective χ) (hm : sizeOf P ≤ m) (hn : sizeOf P ≤ n) :
    Proc.freeChansFuel n (Proc.renameFuel m ν χ ξ P) =
      (Proc.freeChansFuel n P).image χ := by
  cases m with
  | zero => cases P <;> simp_all
  | succ m =>
    cases n with
    | zero => cases P <;> simp_all
    | succ n =>
      cases P with
      | request a k ss P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_sdiff _ _ hχ]
      | accept a k ss P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_sdiff _ _ hχ]
      | send c es P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp
      | recv c xs P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp
      | deleg c ss P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_union]
      | srecv c ss P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_sdiff _ _ hχ]
      | sel c l P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp
      | resN a P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        exact freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)
      | resS ss P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_sdiff _ _ hχ]
      | branch c bs =>
        simp only [Proc.renameFuel, Proc.freeChansFuel, Finset.image_insert]
        congr 1
        simpa using fold_support_image bs
          (fun x ↦ (x.1, Proc.renameFuel m ν χ ξ x.2))
          (fun x ↦ Proc.freeChansFuel n x.2) (fun x ↦ Proc.freeChansFuel n x.2) χ
          (fun x hx ↦ freeChansFuel_rename x.2 m n ν χ ξ hχ
            (by have h := List.sizeOf_lt_of_mem hx; cases x; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hx; cases x; simp_all; omega)) ∅
      | ite e P Q =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega),
          freeChansFuel_rename Q m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [Finset.image_union]
      | par P Q =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega),
          freeChansFuel_rename Q m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [Finset.image_union]
      | nil => simp [Proc.renameFuel, Proc.freeChansFuel]
      | call X es ss =>
        simp [Proc.renameFuel, Proc.freeChansFuel, list_toFinset_map]
      | queue c h =>
        simp only [Proc.renameFuel, Proc.freeChansFuel, Finset.image_insert]
        congr 1
        simpa using fold_support_image h (Msg.rename ν χ) Msg.freeChans Msg.freeChans χ
          (fun x _ ↦ msg_chans_rename x ν χ) ∅
      | defn D P =>
        simp only [Proc.renameFuel, Proc.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        have hd := fold_support_image D (Decl.renameFuel m ν χ ξ)
          (Decl.freeChansFuel n) (Decl.freeChansFuel n) χ
          (fun d hd ↦ freeChansDeclFuel_rename d m n ν χ ξ hχ
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)
            (by have h := List.sizeOf_lt_of_mem hd; simp_all; omega)) ∅
        simpa [Finset.image_union] using congrArg (fun s ↦ (Proc.freeChansFuel n P).image χ ∪ s) hd
termination_by m

theorem freeChansDeclFuel_rename (d : Decl) (m n : Nat)
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hχ : Function.Injective χ) (hm : sizeOf d ≤ m) (hn : sizeOf d ≤ n) :
    Decl.freeChansFuel n (Decl.renameFuel m ν χ ξ d) =
      (Decl.freeChansFuel n d).image χ := by
  cases d with
  | mk X xs ss P =>
    cases m with
    | zero => simp_all
    | succ m =>
      cases n with
      | zero => simp_all
      | succ n =>
        simp only [Decl.renameFuel, Decl.freeChansFuel]
        rw [freeChansFuel_rename P m n ν χ ξ hχ (by simp_all; omega) (by simp_all; omega)]
        simp [list_toFinset_map, Finset.image_sdiff _ _ hχ]
termination_by m
end

theorem freeChans_rename (P : Proc) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (hχ : Function.Injective χ) :
    (P.rename ν χ ξ).freeChans = P.freeChans.image χ := by
  let Q := P.rename ν χ ξ
  let n := max (sizeOf P) (sizeOf Q)
  rw [Proc.freeChans, ← freeChansFuel_stable Q n (sizeOf Q) (Nat.le_max_right _ _) le_rfl]
  change Proc.freeChansFuel n (Proc.renameFuel (sizeOf P) ν χ ξ P) = P.freeChans.image χ
  rw [freeChansFuel_rename P (sizeOf P) n ν χ ξ hχ le_rfl (Nat.le_max_left _ _)]
  rw [freeChansFuel_stable P n (sizeOf P) (Nat.le_max_left _ _) le_rfl]
  rfl

theorem freeChansDecl_rename (d : Decl) (ν : Name → Name) (χ : Chan → Chan)
    (ξ : PVar → PVar) (hχ : Function.Injective χ) :
    (renameDecl d ν χ ξ).freeChans = d.freeChans.image χ := by
  let e := renameDecl d ν χ ξ
  let n := max (sizeOf d) (sizeOf e)
  rw [Decl.freeChans, ← freeChansDeclFuel_stable e n (sizeOf e) (Nat.le_max_right _ _) le_rfl]
  change Decl.freeChansFuel n (Decl.renameFuel (sizeOf d) ν χ ξ d) = d.freeChans.image χ
  rw [freeChansDeclFuel_rename d (sizeOf d) n ν χ ξ hχ le_rfl (Nat.le_max_left _ _)]
  rw [freeChansDeclFuel_stable d n (sizeOf d) (Nat.le_max_left _ _) le_rfl]
  rfl

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

/-- Congruence equivariance and inverse renaming give the two exact target equivalences
needed by the shared-head invariant, including traversals with any sufficient fuel. -/
theorem simpleTargetRename_of_congr_rename
    (hR : ∀ (ν : Name ≃ Name) (χ : Chan ≃ Chan) (ξ : PVar ≃ PVar)
      {P Q : Proc}, Congr P Q → Congr (P.rename ν χ ξ) (Q.rename ν χ ξ))
    (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hν : Function.Bijective ν) (hχ : Function.Bijective χ) (hξ : Function.Bijective ξ) :
    SimpleTargetRename ν χ ξ := by
  let eν : Name ≃ Name := Equiv.ofBijective ν hν
  let eχ : Chan ≃ Chan := Equiv.ofBijective χ hχ
  let eξ : PVar ≃ PVar := Equiv.ofBijective ξ hξ
  change SimpleTargetRename eν eχ eξ
  constructor
  · intro fuel P hf
    rw [renameFuel_eq_rename P fuel eν eχ eξ hf]
    constructor
    · intro h
      simpa using hR eν.symm eχ.symm eξ.symm h
    · intro h
      simpa using hR eν eχ eξ h
  · intro fuel P c hf
    rw [renameFuel_eq_rename P fuel eν eχ eξ hf]
    constructor
    · intro h
      simpa using hR eν.symm eχ.symm eξ.symm h
    · intro h
      simpa using hR eν eχ eξ h

/-- Structural congruence is invariant under simultaneous bijective identifier renaming. -/
theorem congr_rename (ν : Name ≃ Name) (χ : Chan ≃ Chan) (ξ : PVar ≃ PVar)
    {P Q : Proc} (h : Congr P Q) : Congr (P.rename ν χ ξ) (Q.rename ν χ ξ) :=
  congr_rename_of_support ν χ ξ
    (fun P ↦ freeNames_rename P ν χ ξ ν.injective)
    (fun P ↦ freeChans_rename P ν χ ξ χ.injective)
    (fun P ↦ freePVars_rename P ν χ ξ ξ.injective)
    (fun d ↦ freeNames_renameDecl d ν χ ξ ν.injective)
    (fun d ↦ freeChansDecl_rename d ν χ ξ χ.injective) h

/-- The shared-head continuation targets are preserved and reflected by renaming. -/
theorem simpleTargetRename (ν : Name → Name) (χ : Chan → Chan) (ξ : PVar → PVar)
    (hν : Function.Bijective ν) (hχ : Function.Bijective χ) (hξ : Function.Bijective ξ) :
    SimpleTargetRename ν χ ξ :=
  simpleTargetRename_of_congr_rename congr_rename ν χ ξ hν hχ hξ

/-- Alpha-conversion preserves the concrete shared-head continuation condition. -/
theorem goodSharedHeads_alpha (P Q : Proc) (h : Alpha P Q) :
    GoodSharedHeads P ↔ GoodSharedHeads Q :=
  goodSharedHeads_alpha_of_transport simpleTargetRename P Q h

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

theorem initial_good_shared_heads : GoodSharedHeads initial := by
  refine ⟨?_, ?_, trivial⟩
  · exact ⟨rfl, 0, rfl, .refl _⟩
  · exact ⟨rfl, 0, rfl, .refl _⟩

/-- The remaining nominal transport obligation is explicit: once good shared heads are
preserved by alpha-conversion, every exposed occurrence belongs to the original LINK. -/
theorem initial_heads_of_alpha
    (hα : ∀ P Q, Alpha P Q → (GoodSharedHeads P ↔ GoodSharedHeads Q))
    (E : Ctx) (R : Proc) (a : Name)
    (hc : Congr initial (E.fill R)) (hs : SharedHead R a) :
    ∃ (E' : Ctx) (S : Proc), Congr initial (E'.fill S) ∧ SharedRedexContains R S a := by
  have ha := initial_exposed_subject E R a hc hs
  subst a
  have hg : GoodSharedHeads R := goodSharedHeads_of_fill E R
    ((goodSharedHeads_congr_of_alpha hα hc).mp initial_good_shared_heads)
  have hcanon := goodSharedHead_canonical hs hg
  refine ⟨.hole, initial, .refl _, 2, [0], .nil, (fun _ => receiver), by decide,
    by decide, rfl, ?_⟩
  rcases hcanon with hrequest | haccept
  · exact Or.inl hrequest
  · exact Or.inr ⟨0, haccept⟩

theorem initial_wellLinked_of_alpha
    (hα : ∀ P Q, Alpha P Q → (GoodSharedHeads P ↔ GoodSharedHeads Q)) :
    WellLinked initial :=
  wellLinked_of_passive_reducts (initial_heads_of_alpha hα)
    (fun _ h => initial_reduct_passive h)

/-- Every exposed shared prefix in every reachable state is part of a LINK redex. -/
theorem initial_wellLinked : WellLinked initial :=
  initial_wellLinked_of_alpha goodSharedHeads_alpha

end MPSTAsync.Progress.Counterexample


set_option autoImplicit false

namespace MPSTAsync.Progress.Counterexample

theorem stuck_passive : Passive stuck := by
  simp [stuck, receiver, Passive]

theorem stuck_not_nil : ¬ Congr stuck .nil := by
  apply visible_not_nil
  rfl

end MPSTAsync.Progress.Counterexample

open MPSTAsync.Progress MPSTAsync.Progress.Counterexample

theorem solution : ¬ (∀ (P : Proc), IsProgram P → Simple P → WellLinked P →
    (∃ Γ q Δ, Γ.WellFormed ∧ RTypedSimple Γ P q Δ ∧
      ∀ a ∈ P.freeNames, ∃ G, (a, ValSort.shared G) ∈ Γ.names) →
    ∀ P', Relation.ReflTransGen Reduces P P' →
      Congr P' .nil ∨ ∃ P'', Reduces P' P'') := by
  intro h
  have hs : Simple initial := ⟨environment, [], [], environment_wf, initial_typed⟩
  have hshared : ∃ Γ q Δ, Γ.WellFormed ∧ RTypedSimple Γ initial q Δ ∧
      ∀ a ∈ initial.freeNames, ∃ G, (a, ValSort.shared G) ∈ Γ.names :=
    ⟨environment, [], [], environment_wf, initial_typed, initial_shared⟩
  have halt := h initial initial_program hs initial_wellLinked hshared
    stuck (Relation.ReflTransGen.single initial_step)
  rcases halt with hnil | ⟨Q, hQ⟩
  · exact stuck_not_nil hnil
  · exact passive_no_reduction hQ stuck_passive
