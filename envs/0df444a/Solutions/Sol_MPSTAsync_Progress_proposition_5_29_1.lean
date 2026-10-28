-- Prove2me | solution 1 for MPSTAsync.Progress.proposition_5_29_1
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-28T01:38:15.102881+00:00
-- url     : https://prove2.me/submissions/e344da7e-5655-435b-9cea-4f346dc93fc9

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

theorem stuck_passive : Passive stuck := by
  simp [stuck, receiver, Passive]

theorem stuck_not_nil : ¬ Congr stuck .nil := by
  apply visible_not_nil
  rfl

theorem stuck_shared :
    ∀ a ∈ stuck.freeNames, ∃ G, (a, ValSort.shared G) ∈ environment.names := by
  simp [stuck, receiver, Proc.freeNames, Proc.freeNamesFuel]

theorem stuck_no_pvars : stuck.freePVars = ∅ := by
  simp [stuck, receiver, Proc.freePVars, Proc.freePVarsFuel]

end MPSTAsync.Progress.Counterexample

open MPSTAsync.Progress MPSTAsync.Progress.Counterexample

theorem solution : ¬ (∀ (Γ : Env), Γ.WellFormed →
    ∀ (P : Proc) (q : List Chan) (Δ : Typing),
    RTypedSimple Γ P q Δ → TypingCoherent Δ → WellLinked P → QueueFull q Δ →
    (∀ a ∈ P.freeNames, ∃ G, (a, ValSort.shared G) ∈ Γ.names) →
    P.freePVars = ∅ → ¬ Congr P .nil → ∃ P', Reduces P P') := by
  intro h
  obtain ⟨Q, hQ⟩ := h environment environment_wf stuck [] [] stuck_typed
    (by simp [TypingCoherent, Typing.WellFormed]) (passive_wellLinked stuck_passive)
    (by simp [QueueFull, Typing.chans]) stuck_shared stuck_no_pvars stuck_not_nil
  exact passive_no_reduction hQ stuck_passive
