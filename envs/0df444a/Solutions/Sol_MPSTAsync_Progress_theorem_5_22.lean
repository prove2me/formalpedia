-- Prove2me | solution 1 for MPSTAsync.Progress.theorem_5_22
-- status  : ACCEPTED   (disprove)
-- author  : @kmehltretter82
-- created : 2026-10-28T01:57:47.942874+00:00
-- url     : https://prove2.me/submissions/3658a627-89b4-4405-b270-991cb426d33b

import Definitions.Def_MPSTAsync_Progress_Activity

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

namespace MPSTAsync.Progress.SafetyCounterexample

open Counterexample

theorem single_family_wf_at (c : Chan) (F : HFamily) (h : F.WellFormed) :
    Typing.WellFormed [([c], F)] := by
  simpa [Typing.WellFormed] using h

theorem single_comp_at (c : Chan) (F H K : HFamily) (h : HFamilyComp F H K) :
    TypingComp [([c], F)] [([c], H)] [([c], K)] := by
  refine ⟨single_family_wf_at c F h.1, single_family_wf_at c H h.2.1,
    single_family_wf_at c K h.2.2.1, ?_, ?_, by simp⟩
  · simp
  · intro x hx
    have hx' : x = ([c], K) := by simpa using hx
    subst x
    exact Or.inr (Or.inr ⟨([c], F), by simp, ([c], H), by simp, rfl, rfl, h⟩)

theorem typing_comp_empty_left (Δ : Typing) (h : Δ.WellFormed) : TypingComp [] Δ Δ := by
  refine ⟨by simp [Typing.WellFormed], h, h, by simp, ?_, by simp⟩
  intro x hx
  exact Or.inr (Or.inl ⟨x, hx, rfl, by simp, rfl⟩)

def sender : Proc := .send 0 [] .nil
def hot : Proc := .resS [0] (.par (.par sender receiver) (.queue 0 []))
def futureSend : Proc := .ite (.val .tt) (.send 1 [] .nil) (.send 1 [] .nil)
def futureRecv : Proc := .ite (.val .tt) (.recv 1 [] .nil) (.recv 1 [] .nil)
def outside : Proc := .par futureSend futureRecv
def process : Proc := .par hot outside

theorem sender_runtime_at (c : Chan) :
    RTyped true environment (.send c [] .nil) [] [([c], [(.pure sendType, 1)])] := by
  apply RTyped.SEND environment c [] [] .nil [([c], [(.pure .stop, 1)])]
    _ [c] 1 1 .stop
  · simp [TypeAt]
  · exact .nil
  · exact ⟨[], [], rfl, rfl⟩
  · exact .INACT _ _ (by simp [Typing.EndOnly, Typing.WellFormed, HFamily.WellFormed])

theorem receiver_runtime_at (c : Chan) :
    RTyped true environment (.recv c [] .nil) [] [([c], [(.pure recvType, 2)])] := by
  apply RTyped.RCV environment c [] [] .nil [([c], [(.pure .stop, 2)])]
    _ [c] 1 2 .stop
  · simp [TypeAt]
  · rfl
  · simp
  · simp
  · exact ⟨[], [], rfl, rfl⟩
  · exact .INACT _ _ (by simp [Typing.EndOnly, Typing.WellFormed, HFamily.WellFormed])

theorem hot_typed : RTyped true environment hot [] [] := by
  have hparts := RTyped.CONC environment sender receiver [] [] _ _ _ (by simp)
    (single_comp _ _ _ endpoints_comp) (sender_runtime_at 0) (receiver_runtime_at 0)
  have hq : RTyped true environment (.queue 0 []) [0] [([0], [])] := by
    apply RTyped.QNIL environment [0] 1 0 [] [] _ (by simp [TypeAt]) (by simp) empty_end
    exact typing_comp_empty_right _ (single_family_wf [] (by simp [HFamily.WellFormed]))
  have hall := RTyped.CONC environment _ _ [] [0] _ _ _ (by simp)
    (single_comp _ _ _ (family_comp_empty_right endpoints endpoints_comp.2.2.1)) hparts hq
  exact .CRES _ [0] _ [0] endpoints _ [] (by simp) rfl endpoints_coherent hall

theorem outside_typed : RTyped true environment outside [] [([1], endpoints)] := by
  have hs : RTyped true environment futureSend [] [([1], [(.pure sendType, 1)])] :=
    .IF _ _ _ _ _ (.BOOL_T _) (sender_runtime_at 1) (sender_runtime_at 1)
  have hr : RTyped true environment futureRecv [] [([1], [(.pure recvType, 2)])] :=
    .IF _ _ _ _ _ (.BOOL_T _) (receiver_runtime_at 1) (receiver_runtime_at 1)
  exact .CONC _ _ _ [] [] _ _ _ (by simp)
    (single_comp_at 1 _ _ _ endpoints_comp) hs hr

theorem process_typed : RTyped true environment process [] [([1], endpoints)] := by
  exact .CONC _ _ _ [] [] [] _ _ (by simp)
    (typing_comp_empty_left _ (single_family_wf_at 1 endpoints endpoints_comp.2.2.1))
    hot_typed outside_typed

theorem process_coherent : TypingCoherent [([1], endpoints)] := by
  exact ⟨single_family_wf_at 1 endpoints endpoints_comp.2.2.1,
    by simpa using endpoints_coherent⟩

theorem hot_rename :
    Congr hot (.resS [1] (.par (.par (.send 1 [] .nil) (.queue 1 []))
      (.recv 1 [] .nil))) := by
  have ha : Congr hot (.resS [1] (.par (.par (.send 1 [] .nil)
      (.recv 1 [] .nil)) (.queue 1 []))) := by
    apply Congr.alpha
    refine ⟨id, Equiv.swap 0 1, id, Function.bijective_id,
      (Equiv.swap 0 1).bijective, Function.bijective_id, ?_, ?_, ?_, ?_⟩
    · intro a ha; rfl
    · simp [hot, sender, receiver, Proc.freeChans, Proc.freeChansFuel]
    · intro X hX; rfl
    · simp [hot, sender, receiver, Proc.rename, Proc.renameFuel]
  apply Congr.trans _ _ _ ha
  apply Congr.resS
  exact .trans _ _ _ (.parAssoc _ _ _) (.trans _ _ _
    (.parRight _ _ _ (.parComm _ _)) (.symm _ _ (.parAssoc _ _ _)))

theorem process_redex : HasRedexAt process 1 := by
  constructor
  · simp [process, hot, outside, futureSend, futureRecv, sender, receiver,
      Proc.freeChans, Proc.freeChansFuel]
  · refine ⟨.parLeft (.resS [1] (.parLeft .hole (.recv 1 [] .nil))) outside,
      .par (.send 1 [] .nil) (.queue 1 []), ?_, ?_⟩
    · exact .parLeft _ _ _ hot_rename
    · exact .SEND _ _ [] _ _ .nil

theorem process_no_active (fuel : Nat) (dir : Direction) :
    ¬ ActivePrefix fuel [] process (.session 1) dir := by
  intro h
  unfold process hot outside futureSend futureRecv sender receiver at h
  aesop (add safe cases ActivePrefix)

theorem process_no_recv : ¬ ActiveRecv process 1 := by
  rintro ⟨fuel, h⟩
  exact process_no_active fuel .receive h

theorem process_no_emit : ¬ ActiveEmit process 1 := by
  rintro ⟨fuel, h⟩
  exact process_no_active fuel .emit h

end MPSTAsync.Progress.SafetyCounterexample

open MPSTAsync.Progress MPSTAsync.Progress.Counterexample
open MPSTAsync.Progress.SafetyCounterexample

theorem solution : ¬ (∀ (Γ : Env), Γ.WellFormed → ∀ (P : Proc)
    (q : List Chan) (Δ : Typing) (c : Chan),
    RTyped true Γ P q Δ → TypingCoherent Δ → HasRedexAt P c →
    (∃ (E : Ctx) (h : List Msg), Congr P (E.fill (.queue c h)) ∧
      ((ActiveRecv P c ∧ E.occ c = 1 ∧ h ≠ []) ∨
       (ActiveEmit P c ∧ E.occ c = 1) ∨
       (ActiveRecv P c ∧ ActiveEmit P c ∧ E.occ c = 2))) ∧
    (∀ (E : Ctx) (R : Proc), Congr P (E.fill R) → ReceivingRedexPart P R c →
      ((∀ (xs : List Name) (Q : Proc), Congr R (.recv c xs Q) →
          ∃ (E' : Ctx) (vs : List Val) (h : List Msg),
            Congr P (E'.fill (.queue c (.vals vs :: h))) ∧ vs.length = xs.length) ∧
       (∀ (ss : List Chan) (Q : Proc), Congr R (.srecv c ss Q) →
          ∃ (E' : Ctx) (ts : List Chan) (h : List Msg),
            Congr P (E'.fill (.queue c (.chans ts :: h))) ∧ ts.length = ss.length) ∧
       (∀ (bs : List (Label × Proc)), Congr R (.branch c bs) →
          ∃ (E' : Ctx) (l : Label) (Q : Proc) (h : List Msg),
            (l,Q) ∈ bs ∧ Congr P (E'.fill (.queue c (.label l :: h))))))) := by
  intro h
  obtain ⟨E, msgs, hcon, hcases⟩ :=
    (h environment environment_wf process [] [([1], endpoints)] 1
      process_typed process_coherent process_redex).1
  rcases hcases with hrecv | hemit | hboth
  · exact process_no_recv hrecv.1
  · exact process_no_emit hemit.1
  · exact process_no_recv hboth.1
