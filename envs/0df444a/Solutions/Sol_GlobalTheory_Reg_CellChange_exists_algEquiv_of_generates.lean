-- Prove2me | solution 1 for GlobalTheory.Reg.CellChange.exists_algEquiv_of_generates
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:54:10.434813+00:00
-- url     : https://prove2.me/submissions/97eaa9a2-9c72-4a6a-af2a-3ea2861e82b9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_Reframe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsLowerMulUpperOfLeadingMinors
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_ExistsFlagCoordinatesCellChangeBirational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.CellChange
open Matrix
namespace GlobalTheory.Reg.CellChange
theorem _root_.solution {κ ι : Type} [Field κ] [Finite ι] (y : ι → FractionRing (MvPolynomial ι κ))
    (hy : ∀ v, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v) ∈
      IntermediateField.adjoin κ (Set.range y)) :
    ∃ e : FractionRing (MvPolynomial ι κ) ≃ₐ[κ] FractionRing (MvPolynomial ι κ),
      ∀ v, e (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
  have htop : IntermediateField.adjoin κ (Set.range y) = ⊤ := by
    have hp : ∀ p : MvPolynomial ι κ, algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) p ∈
        IntermediateField.adjoin κ (Set.range y) := by
      intro p
      induction p using MvPolynomial.induction_on with
      | C a =>
        rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
        exact IntermediateField.algebraMap_mem _ a
      | add p q hp hq => rw [map_add]; exact add_mem hp hq
      | mul_X p v hp => rw [map_mul]; exact mul_mem hp (hy v)
    rw [eq_top_iff]
    intro x _
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial ι κ) x
    exact div_mem (hp a) (hp b)
  have hX : AlgebraicIndependent κ (fun v : ι =>
      algebraMap (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)) (MvPolynomial.X v)) :=
    (MvPolynomial.algebraicIndependent_X ι κ).map'
      (f := IsScalarTower.toAlgHom κ (MvPolynomial ι κ) (FractionRing (MvPolynomial ι κ)))
      (IsFractionRing.injective _ _)
  have halg : Algebra.IsAlgebraic (Algebra.adjoin κ (Set.range y)) (FractionRing (MvPolynomial ι κ)) := by
    rw [← IntermediateField.isAlgebraic_adjoin_iff_top, htop]
    exact ⟨fun x => isAlgebraic_algebraMap (⟨x, trivial⟩ : (⊤ : IntermediateField κ _))⟩
  have hind : AlgebraicIndependent κ y :=
    (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite κ y hX.cardinalMk_le_trdeg).1
  have hinj : Function.Injective (MvPolynomial.aeval y : MvPolynomial ι κ →ₐ[κ] _) :=
    algebraicIndependent_iff_injective_aeval.1 hind
  let f : FractionRing (MvPolynomial ι κ) →ₐ[κ] FractionRing (MvPolynomial ι κ) :=
    IsFractionRing.liftAlgHom hinj
  have hf : ∀ v, f (algebraMap (MvPolynomial ι κ) _ (MvPolynomial.X v)) = y v := by
    intro v
    simp [f]
  have hs : Function.Surjective f := by
    have : IntermediateField.adjoin κ (Set.range y) ≤ f.fieldRange := by
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨v, rfl⟩
      exact ⟨_, hf v⟩
    intro x
    exact this (htop ▸ IntermediateField.mem_top)
  exact ⟨AlgEquiv.ofBijective f ⟨f.injective, hs⟩, hf⟩
end GlobalTheory.Reg.CellChange
