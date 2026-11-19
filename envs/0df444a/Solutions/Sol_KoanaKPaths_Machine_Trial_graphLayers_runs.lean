-- Prove2me | solution 1 for KoanaKPaths.Machine.Trial.graphLayers_runs
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-18T08:45:20.432479+00:00
-- url     : https://prove2.me/submissions/edf2d675-dc3b-4f1f-a366-4e0acc0fce84

import Definitions.Def_HypergraphUnreliability_FPRAS_Machine
import Definitions.Def_IntMul_SS_Defs1
import Definitions.Def_IntMul_SS_Defs2
import Definitions.Def_KoanaKPaths_BitStackAdapter
import Definitions.Def_KoanaKPaths_ExteriorCoordinates
import Definitions.Def_KoanaKPaths_GraphDP
import Definitions.Def_KoanaKPaths_Main_Estimator
import Definitions.Def_KoanaKPaths_Runtime_LiftNative
import Definitions.Def_KoanaKPaths_Runtime_NatParser
import Definitions.Def_KoanaKPaths_Runtime_NativeProgram
import Definitions.Def_KoanaKPaths_Runtime_SubsetArrays
import Definitions.Def_KoanaKPaths_Runtime_TrialIndexing
import Definitions.Def_KoanaKPaths_TapeSampling
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Size
import Theorems.Thm_KoanaKPaths_Machine_Trial_firstLayer_runs
import Theorems.Thm_KoanaKPaths_Machine_Trial_layerDriver_runs
import Theorems.Thm_KoanaKPaths_Main_graph_dp_sketch
import Theorems.Thm_NLogN_compile_correct
import Theorems.Thm_NLogN_smul_runs
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 8192
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
section

namespace KoanaKPaths.Machine.Native
open NLogN
variable {S P : ℕ} {I : List Sym} {iprog : Fin P→IStmt S P} {p q : IStmt S P} {s s1 s2 : IState S} {c d : ℕ}





lemma seq (h1 : IRuns I iprog p s s1 c) (h2 : IRuns I iprog q s1 s2 d) :
    IRuns I iprog (.seq p q) s s2 (c+d) := by
  obtain ⟨c',hc,h1⟩ := h1
  obtain ⟨d',hd,h2⟩ := h2
  exact ⟨c'+d',Nat.add_le_add hc hd,.seq h1 h2⟩





end KoanaKPaths.Machine.Native

end

section

set_option maxHeartbeats 1000000
open NLogN
namespace KoanaKPaths.Machine

variable {S : ℕ}



@[simp] lemma upd_G_self (s : IState S) (i : Fin S) (L : List Item) : (s.upd i L).G i = L := by
  simp [IState.upd]
@[simp] lemma upd_G_ne (s : IState S) {i j : Fin S} (h : j ≠ i) (L : List Item) :
    (s.upd i L).G j = s.G j := by simp [IState.upd,h]


@[simp] lemma upd_upd (s : IState S) (i : Fin S) (L M : List Item) :
    (s.upd i L).upd i M = s.upd i M := by
  cases s
  simp [IState.upd,Function.update_idem]




















end KoanaKPaths.Machine

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main







lemma Ready.at {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)}
    (h : Ready (k := k) s arcs) (j : Fin NS) (hj : j∈readyRegisters) : s.G j=readyStack n k arcs j := h j hj



lemma Ready.core {n k : ℕ} {s : IState NS} {arcs : List (Fin n × Fin n)}
    (h : Ready (k := k) s arcs) (ω : Fin (trialBits n k)→Bool) (p : ℕ) :
    Core (((s.upd 63 [.int (trialBits n k : ℤ)]).upd 24 (signItems (signsOf ω))).upd 14
      (ArrayLookup.frames (matrixArrays (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 p)))) ω arcs p := by
  intro j hj
  simp only [coreRegisters,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hj
  rcases hj with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
    (try simp [IState.upd,coreStack,NS,Wedge.NS])
  all_goals exact h.at _ (by decide)

end KoanaKPaths.Machine.Trial

end

section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open NLogN
namespace KoanaKPaths.Machine.Trial
open KoanaKPaths.Main
attribute [local simp] Total SignDB SignLookup.DB SignLookup.Count SignLookup.Back SignLookup.Tmp BitCounter.Count BitCounter.Tmp
  VerticesTemplate VerticesCounter LabelCounter LabelTmp PredecessorCounter PreviousCounter LayersCounter
  Matrix.Template Matrix.Counter Matrix.CopyTmp Matrix.Prev ArrayLookup.DB Wedge.D Wedge.HC Wedge.DC Wedge.Aux





lemma graphLayers_runs (I : List Sym) (base : IState NS) {n k : ℕ}
    (ω : Fin (trialBits n k)→Bool) (arcs : List (Fin n × Fin n)) (hk : 1≤ k)
    (hr : Ready (k := k) base arcs) :
    IRuns I Wedge.prog graphLayers (labeledState base ω)
      ((labeledState base ω).upd Matrix.Prev (ArrayLookup.frames (matrixArrays
        (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k))))
      (firstLayerCost n k+layerDriverCost n k arcs.length) := by
  let s := labeledState base ω
  let s1 := s.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
    (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 1)))
  have h0 : IRuns I Wedge.prog firstLayer s s1 (firstLayerCost n k) := by
    have h := firstLayer_runs I s ω arcs [] [] [] []
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 53 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 54 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 59 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 87 (by decide))
      (by simp [s,labeledState]) (by simp [s,labeledState])
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 40 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 41 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 27 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 28 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 29 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 3 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 88 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 89 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 10 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 11 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 12 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 45 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 67 (by decide))
      (by simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 68 (by decide))
    have hp : s.G Matrix.Prev=[] := by
      simpa [s,labeledState,readyStack,NS,Wedge.NS] using hr.at 14 (by decide)
    simpa [s1,hp] using h
  have hCore : Core s1 ω arcs 1 := hr.core ω 1
  have h1 : IRuns I Wedge.prog layerDriver s1
      (s.upd Matrix.Prev (ArrayLookup.frames (matrixArrays
        (denseLayer arcs (trialEquiv n k ω).1 (trialEquiv n k ω).2 k))))
      (layerDriverCost n k arcs.length) := by
    have h := layerDriver_runs I s1 ω arcs [] hk hCore
      (by simpa [s1,s,labeledState,readyStack,NS,Wedge.NS] using hr.at 66 (by decide))
      (by simpa [s1,s,labeledState,readyStack,NS,Wedge.NS] using hr.at 93 (by decide))
      (by simpa [s1,s,labeledState,readyStack,NS,Wedge.NS] using hr.at 87 (by decide))
      (by simpa [s1,s,labeledState,readyStack,NS,Wedge.NS] using hr.at 88 (by decide))
      (by simpa [s1,s,labeledState,readyStack,NS,Wedge.NS] using hr.at 91 (by decide))
      (by simpa [s1,s,labeledState,readyStack,NS,Wedge.NS] using hr.at 92 (by decide))
    simpa [s1] using h
  exact Native.seq h0 h1

end KoanaKPaths.Machine.Trial

end

theorem solution :
∀ (I : List.{0} NLogN.Sym) (base : NLogN.IState KoanaKPaths.Machine.Trial.NS) {n k : Nat}
  (ω : Fin (KoanaKPaths.Main.trialBits n k) → Bool) (arcs : List.{0} (Prod.{0, 0} (Fin n) (Fin n)))
  (hk : @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) k)
  (hr : @KoanaKPaths.Machine.Trial.Ready n k base arcs),
  @NLogN.IRuns KoanaKPaths.Machine.Wedge.NS (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1))) I
    KoanaKPaths.Machine.Wedge.prog KoanaKPaths.Machine.Trial.graphLayers
    (@KoanaKPaths.Machine.Trial.labeledState n k base ω)
    (@NLogN.IState.upd KoanaKPaths.Machine.Trial.NS (@KoanaKPaths.Machine.Trial.labeledState n k base ω)
      KoanaKPaths.Machine.Matrix.Prev
      (KoanaKPaths.Machine.ArrayLookup.frames
        (@KoanaKPaths.Main.matrixArrays n k
          (@KoanaKPaths.Main.denseLayer n k k arcs
            (@Prod.fst.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                  Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                (KoanaKPaths.Main.trialEquiv n k) ω))
            (@Prod.snd.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)
              (@DFunLike.coe.{1, 1, 1}
                (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                (fun (x : Fin (KoanaKPaths.Main.trialBits n k) → Bool) =>
                  Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                (@EquivLike.toFunLike.{1, 1, 1}
                  (Equiv.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k)))
                  (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                  (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))
                  (@Equiv.instEquivLike.{1, 1} (Fin (KoanaKPaths.Main.trialBits n k) → Bool)
                    (Prod.{0, 0} (KoanaKPaths.Main.Labels n k) (KoanaKPaths.Main.SketchSigns n k k))))
                (KoanaKPaths.Main.trialEquiv n k) ω))
            k))))
    (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (KoanaKPaths.Machine.Trial.firstLayerCost n k)
      (KoanaKPaths.Machine.Trial.layerDriverCost n k (@List.length.{0} (Prod.{0, 0} (Fin n) (Fin n)) arcs))) := by
  exact @KoanaKPaths.Machine.Trial.graphLayers_runs
