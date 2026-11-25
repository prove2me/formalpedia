-- Prove2me | solution 1 for GlobalTheory.exists_factor_integralClosure_of_finiteType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:56:53.800449+00:00
-- url     : https://prove2.me/submissions/7a8d7e11-5adb-485c-90fe-8a5625f62993

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsDiscreteValuationRingIntegralClosurePadicInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MemPadicAlgClValuationSubringIffNormLeOne
import Theorems.Thm_GlobalTheory_mem_integralClosure_padicInt_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))
open GlobalTheory
variable {p : ℕ} [Fact p.Prime]
namespace GlobalTheory
theorem _root_.solution {A : Type*} [CommRing A]
    [Algebra.FiniteType ℤ A] (φ : A →+* OO p) :
    ∃ K₀ : IntermediateField ℚ_[p] (PadicAlgCl p), FiniteDimensional ℚ_[p] K₀ ∧
      ∀ K : IntermediateField ℚ_[p] (PadicAlgCl p), K₀ ≤ K →
        ∃ ψ : A →+* integralClosure ℤ_[p] K,
          (integralClosureToPadicAlgClIntegers K).comp ψ = φ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := ℤ) (A := A)
  let φ' : A →+* PadicAlgCl p := (OO p).subtype.comp φ
  refine ⟨IntermediateField.adjoin ℚ_[p] ((s.image φ' : Finset _) : Set (PadicAlgCl p)),
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x,
    fun K hK => ?_⟩
  have hmem : ∀ a, φ' a ∈ K := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (s : Set A) := hs ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem x hx =>
      exact hK (IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩))
    | algebraMap r => simp
    | add x y _ _ hx hy => rw [map_add]; exact K.add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact K.mul_mem hx hy
  let ψ₁ : A →+* K := φ'.codRestrict K hmem
  refine ⟨ψ₁.codRestrict (integralClosure ℤ_[p] K) fun a =>
    (mem_integralClosure_padicInt_iff K _).mpr
      ((mem_padicAlgCl_valuationSubring_iff_norm_le_one _).mp (φ a).2), ?_⟩
  ext a
  rfl
end GlobalTheory
