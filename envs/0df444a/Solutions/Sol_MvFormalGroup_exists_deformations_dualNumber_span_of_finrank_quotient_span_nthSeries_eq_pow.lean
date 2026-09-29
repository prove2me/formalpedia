-- Prove2me | solution 1 for MvFormalGroup.exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/7c2753a6-ac72-5e4c-a536-e1624cddf02f

import Mathlib
import Definitions.Def_MvFormalGroup_TwoCocycle
import Theorems.Thm_MvFormalGroup_exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle
import Theorems.Thm_MvFormalGroup_exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing MvFormalGroup.End.instMonoid MvFormalGroup.End.instSemiring MvFormalGroup.End.instAddCommMonoid MvFormalGroup.Hom.instZero MvFormalGroup.Hom.instAdd MvFormalGroup.Hom.instAddCommMonoid instTopologicallyFGOfFiniteType MvFormalGroup.Points.instNeg MvFormalGroup.Points.instZero MvFormalGroup.Points.instAdd MvFormalGroup.Points.instAddCommGroup MvFormalGroup.Points.instAddGroup MonoidAlgebra.instModuleFiniteOfCartier CartierDual.instCoalgebra CartierDual.instModuleFinite CartierDual.instBialgebra CartierDual.instFunLike CartierDual.instRing CartierDual.instLinearMapClass CartierDual.instCommRing CartierDual.instIsCocomm MonoidAlgebra.instModuleFreeOfCartier CartierDual.instModuleFree CartierDual.instHopfAlgebra CartierDual.instAlgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg' MvFormalGroup.linearPartHom_apply MvFormalGroup.linearPart_zero MvFormalGroup.linearPart_X MvFormalGroup.End.toPowerSeries_mul MvFormalGroup.Hom.toPowerSeries_add MvFormalGroup.End.toPowerSeries_add MvFormalGroup.End.toPowerSeries_one MvFormalGroup.End.toPowerSeries_zero MvFormalGroup.Hom.toPowerSeries_zero MvFormalGroup.linearPartHom_natCast MvFormalGroup.Hom.toPowerSeries_zero' MvFormalGroup.End.toPowerSeries_natCast MvFormalGroup.Points.mk.injEq MvFormalGroup.Points.mk.sizeOf_spec ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq Deformation.DieudonneDatum.mk.sizeOf_spec Deformation.HondaSystem.mk.injEq Deformation.DieudonneDatum.mk.injEq Deformation.HondaSystem.mk.sizeOf_spec CartierDual.toDual_ofDual CartierDual.algebraMap_apply CartierDual.antipode_apply CartierDual.one_apply CartierDual.toDual_apply CartierDual.ofDual_toDual CartierDual.ofDual_apply CartierDual.counit_apply CartierDual.map_apply"
p2m_attr_erase "simp" "CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul"

set_option autoImplicit false

universe u

open DualNumber in
theorem solution
    {k : Type u} [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
    {n : ℕ} (F₀ : MvFormalGroup n k) [F₀.IsComm] (h : ℕ)
    (hh : Module.finrank k (MvPowerSeries (Fin n) k ⧸ Ideal.span (Set.range (F₀.nthSeries p))) = p ^ h) :
    ∃ (d : ℕ) (D : Fin d → MvFormalGroup n (DualNumber k)),
      d ≤ n * (h - n) ∧
      (∀ j, (D j).IsComm ∧ (D j).map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀) ∧
      ∀ (F : MvFormalGroup n (DualNumber k)) [F.IsComm],
        F.map (TrivSqZeroExt.fstHom k k k).toRingHom = F₀ →
        ∃ (c : Fin d → k) (G : MvFormalGroup n (DualNumber k)) (θ : G.Hom F),
          (∀ i, G.toPowerSeries i =
            MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i) +
              ∑ j, c j • ((D j).toPowerSeries i -
                MvPowerSeries.map (TrivSqZeroExt.inlHom k k) (F₀.toPowerSeries i))) ∧
          ∀ i, MvPowerSeries.map (TrivSqZeroExt.fstHom k k k).toRingHom (θ.toPowerSeries i) =
            MvPowerSeries.X i := by
  obtain ⟨r, Γ, hr, hΓ, hspan⟩ :=
    MvFormalGroup.exists_isSymmTwoCocycle_span_of_finrank_quotient_span_nthSeries_eq_pow p F₀ h hh
  obtain ⟨d, D, hd, hD, hall⟩ :=
    MvFormalGroup.exists_deformations_dualNumber_span_of_forall_isSymmTwoCocycle F₀ r Γ hΓ hspan
  exact ⟨d, D, hd.trans (Nat.mul_le_mul_left n hr), hD, fun F _ hF => hall F hF⟩

end S_MvFormalGroup_exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow
end P2MW
export P2MW.S_MvFormalGroup_exists_deformations_dualNumber_span_of_finrank_quotient_span_nthSeries_eq_pow (solution)
