-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_general
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T08:41:11.376796+00:00
-- url     : https://prove2.me/submissions/b5ef878d-60cf-43d4-ac93-c8cc7e0cde6e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/IntervalPacking.lean:L424-L485
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_general. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail
import Definitions.Def_OAI_Analysis_Littlewood_Spreading
import Definitions.Def_OAI_Analysis_Littlewood_ProductProbability
import Definitions.Def_OAI_Analysis_Littlewood_Nibble
import Definitions.Def_OAI_Analysis_Littlewood_Averages
import Definitions.Def_OAI_Analysis_Littlewood_FiniteRank
import Definitions.Def_OAI_Analysis_Littlewood_Chunks
import Definitions.Def_OAI_Analysis_Littlewood_DependentMoments
import Definitions.Def_OAI_Analysis_Littlewood_SlotGraph
import Definitions.Def_OAI_Analysis_Littlewood_SlotParameters
import Definitions.Def_OAI_Analysis_Littlewood_IntervalPacking
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_Packing_signed_interval_packing

-- ---- from OAI.Analysis.Littlewood.IntervalPacking ----
namespace OAI

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset Nibble Filter Topology
attribute [local instance] Classical.propDecidable

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

end
end AsymptoticallyMinimalLittlewood.Packing

namespace AsymptoticallyMinimalLittlewood.Packing
noncomputable section
open scoped BigOperators
open Finset

lemma signed_interval_packing_fintype {I J : Type} [Fintype I] [Fintype J]
    (hr : 2≤Fintype.card I) (a : I → J → ℤ)
    (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  let E := Fintype.equivFin I
  let F := Fintype.equivFin J
  let A (i : Fin (Fintype.card I)) (k : Fin (Fintype.card J)) := a (E.symm i) (F.symm k)
  have hA (i) : (fun k ↦ (A i k : ℚ))≠0 := by
    intro hz
    apply ha (E.symm i)
    funext k
    have hh := congrFun hz (F k)
    simpa only [A,Equiv.symm_apply_apply,Pi.zero_apply,Int.cast_eq_zero] using hh
  have hNP (i j) (hij : i≠j) (c : ℚ) :
      (fun k ↦ (A j k : ℚ))≠c • (fun k ↦ (A i k : ℚ)) := by
    intro he
    apply hnp (E.symm i) (E.symm j) (fun h ↦ hij (E.symm.injective h)) (c : ℝ)
    intro k
    have hh := congrFun he (F k)
    simp only [A,Equiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul] at hh
    exact_mod_cast hh
  obtain ⟨H,hH,θ,hθ⟩ := signed_interval_packing hr A hA hNP (w ∘ E.symm)
    (fun i ↦ hw _) (by simpa only [Function.comp_apply,Equiv.sum_comp] using hs)
  refine ⟨H,hH,(fun h k ↦ θ h (F k)),?_⟩
  intro e f i j h v hne
  have hh := hθ e f (E i) (E j) h v (by
    intro he
    apply hne
    obtain ⟨hef,hij,hv⟩ := Prod.mk.inj he |>.imp id Prod.mk.inj
    exact Prod.ext hef (Prod.ext (E.injective hij) hv))
  simpa only [A,Function.comp_apply,Equiv.symm_apply_apply,← Equiv.sum_comp F] using hh

/-- The minor degenerate-cardinality case is absorbed by a zero-coefficient
fresh frequency. Only geometry is padded; the auxiliary polynomial is unchanged. -/
theorem signed_interval_packing_general {I J : Type} [Fintype I] [Fintype J]
    [Nonempty I] (a : I → J → ℤ) (ha : ∀ i, a i≠0)
    (hnp : ∀ i j, i≠j → ∀ c : ℝ, ¬∀ k, (a j k : ℝ)=c*(a i k : ℝ))
    (w : I → ℝ) (hw : ∀ i, 0<w i) (hs : 2*∑ i, w i<1) :
    ∃ H : ℕ, 1≤H ∧ ∃ θ : Fin H → J → UnitAddCircle,
      ∀ e f : Bool, ∀ i j : I, ∀ h v : Fin H, (e,i,h)≠(f,j,v) →
        Disjoint (circleInterval (signedCircle e (∑ k, a i k • θ h k)) (w i/H))
          (circleInterval (signedCircle f (∑ k, a j k • θ v k)) (w j/H)) := by
  classical
  let A : Option I → Option J → ℤ := fun i k ↦ match i,k with
    | none,none => 1 | some i,some k => a i k | _,_ => 0
  let W : Option I → ℝ := fun i ↦ match i with
    | none => (1-2*∑ i, w i)/4 | some i => w i
  have hcard : 2≤Fintype.card (Option I) := by
    rw [Fintype.card_option]
    have := Fintype.card_pos_iff.mpr (inferInstance : Nonempty I)
    omega
  have hA (i : Option I) : A i≠0 := by
    cases i with
    | none => intro h; have := congrFun h none; simp [A] at this
    | some i =>
      intro h
      apply ha i
      funext k
      have := congrFun h (some k)
      simpa [A] using this
  have hNP (i j : Option I) (hij : i≠j) (c : ℝ) :
      ¬∀ k, (A j k : ℝ)=c*(A i k : ℝ) := by
    intro he
    cases i with
    | none =>
      cases j with
      | none => exact hij rfl
      | some j =>
        apply ha j
        funext k
        have hh := he (some k)
        simpa [A] using hh
    | some i =>
      cases j with
      | none => have hh := he none; norm_num [A] at hh
      | some j =>
        exact hnp i j (fun h ↦ hij (congrArg some h)) c (fun k ↦ by simpa [A] using he (some k))
  have hW (i : Option I) : 0<W i := by
    cases i with
    | none => dsimp [W]; linarith
    | some i => exact hw i
  have hsum : 2*∑ i, W i<1 := by
    rw [Fintype.sum_option]
    change 2*((1-2*∑ i, w i)/4+∑ i, w i)<1
    linarith
  obtain ⟨H,hH,θ,hθ⟩ := signed_interval_packing_fintype hcard A hA hNP W hW hsum
  refine ⟨H,hH,(fun h k ↦ θ h (some k)),?_⟩
  intro e f i j h v hne
  have hh := hθ e f (some i) (some j) h v (by
    intro he
    apply hne
    obtain ⟨hef,hij,hv⟩ := Prod.mk.inj he |>.imp id Prod.mk.inj
    exact Prod.ext hef (Prod.ext (Option.some.inj hij) hv))
  simpa only [Fintype.sum_option,A,zero_smul,zero_add,W] using hh

end
end AsymptoticallyMinimalLittlewood.Packing

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.Packing
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_general := @_root_.OAI.AsymptoticallyMinimalLittlewood.Packing.signed_interval_packing_general
