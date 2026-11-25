-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity.isOpen_lat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:53:15.693594+00:00
-- url     : https://prove2.me/submissions/850cb992-6cfa-4e42-b194-c1de02ea9569

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_IndicatorFunctionIdentity
import Theorems.Thm_GlobalTheory_SplitWeil_isOpen_int

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
open GlobalTheory.SplitWeil GlobalTheory.LatPair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
private lemma isOpen_stdLat : IsOpen (stdLat k n : Set (n → k)) := by
  have e : (stdLat k n : Set (n → k)) = Set.univ.pi fun _ => (𝒪[k] : Set k) := by
    ext x
    simp [mem_stdLat]
  rw [e]
  exact isOpen_set_pi Set.finite_univ fun _ _ => isOpen_int k
variable {V' V : Type} [AddCommGroup V'] [Module ℂ V'] [AddCommGroup V] [Module ℂ V]
variable {μ : kˣ →* ℂˣ} {π' : Representation ℂ (GL n' k) V'} {π : Representation ℂ (GL n k) V}
  {θ : V' →ₗ[ℂ] SB (Matrix n n' k) →ₗ[ℂ] V}
example (hμ : IsUnram μ) (hθ : IsEquivTheta μ π' π θ) (P₀ : Pair k n') (Q₀ : Pair k n) (φ : EqForm π') :
    (K hμ hθ P₀ Q₀ φ).1 Q₀ = θ (φ.1 P₀) (phiOneSB P₀ Q₀) := by
  simpa using K_apply hμ hθ P₀ Q₀ φ 1
example (t : ℕ) : scal k t ^ 2 = (resCard k : ℂ) ^ (t + 1) := by
  rw [scal, ← Complex.ofReal_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  rw [show ((t : ℝ) + 1) / 2 * (2 : ℕ) = ((t + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  push_cast
  rfl
end GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
end
end

set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
open GlobalTheory.SplitWeil GlobalTheory.LatPair
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
namespace GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
theorem _root_.solution (L : Submodule 𝒪[k] (n → k)) [L.IsLattice k] : IsOpen (L : Set (n → k)) := by
  obtain ⟨g, rfl⟩ := exists_smul_lat (stdLat k n) L
  have e : ((g • stdLat k n : Submodule 𝒪[k] (n → k)) : Set (n → k)) =
      (fun x => (g⁻¹ : GL n k).val *ᵥ x) ⁻¹' (stdLat k n : Set (n → k)) := by
    ext x
    exact mem_smul_iff
  rw [e]
  exact isOpen_stdLat.preimage (Continuous.matrix_mulVec continuous_const continuous_id)
end GlobalTheory.IndefiniteRowSideFullHecke.IndicatorFunctionIdentity
