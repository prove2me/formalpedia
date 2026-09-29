-- Prove2me | solution 1 for MvPowerSeries.existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/feb8f545-0142-5e12-91ec-c9e19e565ae3

import Mathlib
import Theorems.Thm_MvPowerSeries_eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue
import Theorems.Thm_MvPowerSeries_exists_eq_sum_subst_mul_of_span_quotient_eq_top
import Theorems.Thm_MvPowerSeries_exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvPowerSeries_existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType"

set_option autoImplicit false

open scoped TensorProduct

theorem solution
    {B : Type} [CommRing B] [IsLocalRing B] [IsNoetherianRing B] {n d : ℕ} (ρ : Fin n → MvPowerSeries (Fin n) B)
    (hρ0 : ∀ i, MvPowerSeries.constantCoeff (ρ i) = 0)
    (hN : ∃ N : ℕ, ∀ i : Fin n, (MvPowerSeries.X i : MvPowerSeries (Fin n) B) ^ N ∈ Ideal.span (Set.range ρ))
    (hfin : Module.Finite B (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ)))
    (b : Fin d → MvPowerSeries (Fin n) B)
    (β : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (TensorProduct B (IsLocalRing.ResidueField B) (MvPowerSeries (Fin n) B ⧸ Ideal.span (Set.range ρ))))
    (hb : ∀ j, β j = TensorProduct.tmul B (1 : IsLocalRing.ResidueField B) (Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)))
    (f : MvPowerSeries (Fin n) B) :
    ∃! c : Fin d → MvPowerSeries (Fin n) B, f = ∑ j, MvPowerSeries.subst ρ (c j) * b j := by
  classical
  haveI := hfin

  have hgen : Submodule.span B (Set.range (fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j))) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis (R := B)
      (f := fun j => Ideal.Quotient.mk (Ideal.span (Set.range ρ)) (b j)) β (fun j => (hb j).symm)

  obtain ⟨e, he⟩ := MvPowerSeries.exists_algEquiv_tensorProduct_quotient_span_map_of_X_pow_mem
    (S := IsLocalRing.ResidueField B) ρ hN
  let β' : Module.Basis (Fin d) (IsLocalRing.ResidueField B)
      (MvPowerSeries (Fin n) (IsLocalRing.ResidueField B) ⧸
        Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i))) :=
    β.map e.toLinearEquiv
  have hβ' : ∀ j, β' j = Ideal.Quotient.mk
      (Ideal.span (Set.range fun i => MvPowerSeries.map (IsLocalRing.residue B) (ρ i)))
      (MvPowerSeries.map (IsLocalRing.residue B) (b j)) := by
    intro j
    show e.toLinearEquiv (β j) = _
    rw [hb j, AlgEquiv.toLinearEquiv_apply, he, one_smul]
    rfl
  obtain ⟨c, hc⟩ := MvPowerSeries.exists_eq_sum_subst_mul_of_span_quotient_eq_top ρ hρ0 b hgen f
  refine ⟨c, hc, fun c' hc' => ?_⟩
  exact MvPowerSeries.eq_of_sum_subst_mul_eq_of_basis_quotient_map_residue ρ hρ0 b β' hβ' c' c (hc' ▸ hc ▸ rfl)

end S_MvPowerSeries_existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient
end P2MW
export P2MW.S_MvPowerSeries_existsUnique_eq_sum_subst_mul_of_basis_residueField_tensor_quotient (solution)
