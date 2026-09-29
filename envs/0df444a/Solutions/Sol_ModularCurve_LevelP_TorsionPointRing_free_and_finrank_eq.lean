-- Prove2me | solution 1 for ModularCurve.LevelP.TorsionPointRing.free_and_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/ff324d78-cbc2-5239-9a34-2e3674e5444b

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPUniversal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq

set_option autoImplicit false

universe u

noncomputable section

open Polynomial

namespace AdjoinRoot
p2m_export "AdjoinRoot" "powerBasis_gen powerBasis' powerBasis of algEquivOfAssociated powerBasis'_gen algEquivOfAssociated_root powerBasis_dim root powerBasis'_dim map"
p2m_open "AdjoinRoot"

variable {R : Type u} [CommRing R] {f : R[X]}

theorem monic_C_unit_inv_mul (hf : IsUnit f.leadingCoeff) :
    (C ((hf.unit⁻¹ : Rˣ) : R) * f).Monic :=
  monic_C_mul_of_mul_leadingCoeff_eq_one (by simp [IsUnit.val_inv_mul])

theorem associated_C_unit_inv_mul (hf : IsUnit f.leadingCoeff) :
    Associated (C ((hf.unit⁻¹ : Rˣ) : R) * f) f := by
  refine ⟨Units.map (C : R →+* R[X]).toMonoidHom hf.unit, ?_⟩
  rw [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, IsUnit.unit_spec,
    mul_comm, ← mul_assoc, ← C_mul, IsUnit.mul_val_inv, C_1, one_mul]

theorem natDegree_C_unit_inv_mul [Nontrivial R] (hf : IsUnit f.leadingCoeff) :
    (C ((hf.unit⁻¹ : Rˣ) : R) * f).natDegree = f.natDegree :=
  natDegree_C_mul_of_mul_ne_zero (by simp [IsUnit.val_inv_mul])

noncomputable def powerBasisOfIsUnitLeadingCoeff (hf : IsUnit f.leadingCoeff) :
    PowerBasis R (AdjoinRoot f) :=
  (powerBasis' (monic_C_unit_inv_mul hf)).map
    (algEquivOfAssociated R _ f (associated_C_unit_inv_mul hf))

theorem powerBasisOfIsUnitLeadingCoeff_dim [Nontrivial R] (hf : IsUnit f.leadingCoeff) :
    (powerBasisOfIsUnitLeadingCoeff hf).dim = f.natDegree := by
  rw [powerBasisOfIsUnitLeadingCoeff, PowerBasis.map_dim, powerBasis'_dim,
    natDegree_C_unit_inv_mul]

@[scoped simp] theorem powerBasisOfIsUnitLeadingCoeff_gen (hf : IsUnit f.leadingCoeff) :
    (powerBasisOfIsUnitLeadingCoeff hf).gen = root f := by
  rw [powerBasisOfIsUnitLeadingCoeff, PowerBasis.map_gen, powerBasis'_gen,
    algEquivOfAssociated_root]

end AdjoinRoot
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq.AdjoinRoot"

namespace ModularCurve
p2m_export "ModularCurve" "LevelP.TorsionPointRing"
namespace LevelP
p2m_export "ModularCurve.LevelP" "PsiRoot PsiRoot.ofBase psiRootX torsionQuadratic TorsionPointRing torsionPtX torsionPtY"
p2m_open "ModularCurve.LevelP ModularCurve"

open Polynomial WeierstrassCurve

variable {B : Type u} [CommRing B] (W : WeierstrassCurve B) {p : ℕ}

theorem natDegree_preΨ_natCast_of_odd [Nontrivial B] (hp : Odd p) (hpu : IsUnit (p : B)) :
    (W.preΨ p).natDegree = (p ^ 2 - 1) / 2 := by
  have h : ((p : ℤ) : B) ≠ 0 := by rw [Int.cast_natCast]; exact hpu.ne_zero
  rw [W.natDegree_preΨ h, Int.natAbs_natCast, if_neg (by simpa using Nat.not_even_iff_odd.mpr hp)]

theorem isUnit_leadingCoeff_preΨ_natCast_of_odd (hp : Odd p) (hpu : IsUnit (p : B)) :
    IsUnit (W.preΨ p).leadingCoeff := by
  nontriviality B
  have h : ((p : ℤ) : B) ≠ 0 := by rw [Int.cast_natCast]; exact hpu.ne_zero
  rw [W.leadingCoeff_preΨ h, if_neg (by simpa using Nat.not_even_iff_odd.mpr hp), Int.cast_natCast]
  exact hpu

namespace PsiRoot p2m_export "ModularCurve.LevelP.PsiRoot" "ofBase" end PsiRoot
p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in
variable (p) in

noncomputable def PsiRoot.powerBasis (hp : Odd p) (hpu : IsUnit (p : B)) :
    PowerBasis B (PsiRoot W p) :=
  AdjoinRoot.powerBasisOfIsUnitLeadingCoeff (isUnit_leadingCoeff_preΨ_natCast_of_odd W hp hpu)

p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in
theorem PsiRoot.powerBasis_dim [Nontrivial B] (hp : Odd p) (hpu : IsUnit (p : B)) :
    (PsiRoot.powerBasis W p hp hpu).dim = (p ^ 2 - 1) / 2 := by
  rw [PsiRoot.powerBasis, AdjoinRoot.powerBasisOfIsUnitLeadingCoeff_dim,
    natDegree_preΨ_natCast_of_odd W hp hpu]

p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in
theorem PsiRoot.powerBasis_gen (hp : Odd p) (hpu : IsUnit (p : B)) :
    (PsiRoot.powerBasis W p hp hpu).gen = psiRootX W p :=
  AdjoinRoot.powerBasisOfIsUnitLeadingCoeff_gen _

variable (p) in
theorem torsionQuadratic_eq_X_pow_add :
    torsionQuadratic W p = X ^ 2 +
      (C (PsiRoot.ofBase W p W.a₁ * psiRootX W p + PsiRoot.ofBase W p W.a₃) * X -
        C (psiRootX W p ^ 3 + PsiRoot.ofBase W p W.a₂ * psiRootX W p ^ 2 +
          PsiRoot.ofBase W p W.a₄ * psiRootX W p + PsiRoot.ofBase W p W.a₆)) := by
  rw [torsionQuadratic, add_sub_assoc]

theorem degree_torsionQuadratic_tail_lt :
    (C (PsiRoot.ofBase W p W.a₁ * psiRootX W p + PsiRoot.ofBase W p W.a₃) * X -
        C (psiRootX W p ^ 3 + PsiRoot.ofBase W p W.a₂ * psiRootX W p ^ 2 +
          PsiRoot.ofBase W p W.a₄ * psiRootX W p + PsiRoot.ofBase W p W.a₆)).degree <
      ((2 : ℕ) : WithBot ℕ) :=
  lt_of_le_of_lt ((degree_sub_le _ _).trans
    (max_le (degree_C_mul_X_le _) (degree_C_le.trans zero_le_one)))
    (WithBot.coe_lt_coe.mpr one_lt_two)

variable (p) in
theorem monic_torsionQuadratic : (torsionQuadratic W p).Monic := by
  rw [torsionQuadratic_eq_X_pow_add]
  exact monic_X_pow_add (degree_torsionQuadratic_tail_lt W)

variable (p) in
theorem natDegree_torsionQuadratic [Nontrivial (PsiRoot W p)] :
    (torsionQuadratic W p).natDegree = 2 := by
  rw [torsionQuadratic_eq_X_pow_add, natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  rw [degree_X_pow]
  exact degree_torsionQuadratic_tail_lt W

namespace TorsionPointRing p2m_export "ModularCurve.LevelP.TorsionPointRing" "ofBase" end TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
variable (p) in

noncomputable def TorsionPointRing.powerBasisOverPsiRoot :
    PowerBasis (PsiRoot W p) (TorsionPointRing W p) :=
  AdjoinRoot.powerBasis' (monic_torsionQuadratic W p)

p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
theorem TorsionPointRing.powerBasisOverPsiRoot_dim [Nontrivial (PsiRoot W p)] :
    (TorsionPointRing.powerBasisOverPsiRoot W p).dim = 2 := by
  rw [TorsionPointRing.powerBasisOverPsiRoot, AdjoinRoot.powerBasis'_dim,
    natDegree_torsionQuadratic]

p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
theorem TorsionPointRing.powerBasisOverPsiRoot_gen :
    (TorsionPointRing.powerBasisOverPsiRoot W p).gen = torsionPtY W p := rfl

p2m_open_scoped "ModularCurve.LevelP.PsiRoot" in
theorem PsiRoot.nontrivial [Nontrivial B] (hp : Odd p) (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Nontrivial (PsiRoot W p) := by
  apply Module.nontrivial_of_finrank_pos (R := B)
  rw [(PsiRoot.powerBasis W p hp hpu).finrank, PsiRoot.powerBasis_dim]
  obtain ⟨k, rfl⟩ := hp
  have hk : k ≠ 0 := by rintro rfl; exact hp1 rfl
  have : (2 * k + 1) ^ 2 - 1 = 2 * (2 * k * (k + 1)) := by
    rw [Nat.sub_eq_of_eq_add]; ring
  rw [this, Nat.mul_div_cancel_left _ two_pos]
  exact Nat.mul_pos (Nat.mul_pos two_pos (Nat.pos_of_ne_zero hk)) k.succ_pos

namespace TorsionPointRing
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
variable (p) in

private noncomputable def _root_.ModularCurve.LevelP.TorsionPointRing.basis (hp : Odd p) (hpu : IsUnit (p : B)) :
    Module.Basis (Fin (PsiRoot.powerBasis W p hp hpu).dim ×
        Fin (TorsionPointRing.powerBasisOverPsiRoot W p).dim) B (TorsionPointRing W p) :=
  (PsiRoot.powerBasis W p hp hpu).basis.smulTower (TorsionPointRing.powerBasisOverPsiRoot W p).basis

end TorsionPointRing
p2m_export "ModularCurve.LevelP" "TorsionPointRing.basis"
p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in
theorem TorsionPointRing.basis_apply (hp : Odd p) (hpu : IsUnit (p : B)) (ij) :
    TorsionPointRing.basis W p hp hpu ij = torsionPtX W p ^ (ij.1 : ℕ) * torsionPtY W p ^ (ij.2 : ℕ) := by
  simp only [TorsionPointRing.basis, Module.Basis.smulTower_apply, PowerBasis.coe_basis,
    PsiRoot.powerBasis_gen, TorsionPointRing.powerBasisOverPsiRoot_gen, Algebra.smul_def, map_pow]
  rfl

p2m_open_scoped "ModularCurve.LevelP.TorsionPointRing" in

theorem TorsionPointRing.free_and_finrank_eq' [Nontrivial B] (hp : Odd p) (hp1 : p ≠ 1)
    (hpu : IsUnit (p : B)) :
    Module.Free B (TorsionPointRing W p) ∧
      Module.finrank B (TorsionPointRing W p) = p ^ 2 - 1 := by
  haveI := PsiRoot.nontrivial W hp hp1 hpu
  let b := TorsionPointRing.basis W p hp hpu
  refine ⟨Module.Free.of_basis b, ?_⟩
  rw [Module.finrank_eq_card_basis b, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
    PsiRoot.powerBasis_dim, TorsionPointRing.powerBasisOverPsiRoot_dim]
  exact Nat.div_mul_cancel (even_iff_two_dvd.mp (Nat.Odd.sub_odd hp.pow odd_one))

end ModularCurve.LevelP
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq.AdjoinRoot"
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq.AdjoinRoot"

end
p2m_reactivate "P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq.AdjoinRoot"

theorem solution
    {B : Type u} [CommRing B] [Nontrivial B] (W : WeierstrassCurve B) {p : ℕ} (hp : Odd p)
    (hp1 : p ≠ 1) (hpu : IsUnit (p : B)) :
    Module.Free B (ModularCurve.LevelP.TorsionPointRing W p) ∧
      Module.finrank B (ModularCurve.LevelP.TorsionPointRing W p) = p ^ 2 - 1 :=
  ModularCurve.LevelP.TorsionPointRing.free_and_finrank_eq' W hp hp1 hpu

end S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq
end P2MW
export P2MW.S_ModularCurve_LevelP_TorsionPointRing_free_and_finrank_eq (solution)
