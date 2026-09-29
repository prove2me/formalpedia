-- Prove2me | solution 1 for ModularCurve.exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/88bad439-d011-5c2b-b04c-115cfb094200

import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionSheaf
import Theorems.Thm_Module_exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar
set_option autoImplicit false
open ModularCurve

theorem solution
    (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hfin : ∀ m : ℕ, Finite ↥(jZeroTorsion p (q ^ m))) :
    letI := heckeModuleBar p
    ∃ t : ℕ → HeckeAlg, ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
      t m • (t m • x) = t m • x ∧ (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m) ∧
        t (m + 1) • x = t m • x := by
  letI := heckeModuleBar p

  let Nq : ℕ → Submodule HeckeAlg (JZero p) := fun m =>
    Submodule.torsionBy HeckeAlg (JZero p) (MvPolynomial.C ((q : ℤ) ^ m))
  have hmem : ∀ (m : ℕ) (x : JZero p), x ∈ Nq m ↔ (q ^ m : ℤ) • x = 0 := by
    intro m x
    rw [Submodule.mem_torsionBy_iff, heckeModuleBar_C_smul]
  haveI hfinN : ∀ m, Finite ↥(Nq m) := by
    intro m
    haveI := hfin m
    refine Finite.of_equiv ↥(jZeroTorsion p (q ^ m)) (Equiv.subtypeEquivRight (fun x => ?_))
    change x ∈ Submodule.torsionBy ℤ (JZero p) ((q ^ m : ℕ) : ℤ) ↔ x ∈ Nq m
    rw [Submodule.mem_torsionBy_iff, hmem, Nat.cast_pow]
  have key := fun m => Module.exists_smul_smul_eq_and_smul_eq_iff_mem_iSup_torsionBySet_pow_of_finite
    (Nq m) (eisensteinMaximalIdeal p q)
  choose t ht1 ht2 using key

  have hprim : ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
      (x ∈ ⨆ k : ℕ, Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg) ↔
        x ∈ eisensteinPrimaryTorsionBar p q m) := by
    intro m x hx
    have hdirS : Directed (· ≤ ·) (fun k : ℕ =>
        Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)) := by
      apply Monotone.directed_le
      intro k l hkl y hy
      rw [Submodule.mem_torsionBySet_iff] at hy ⊢
      rintro ⟨a, ha⟩
      exact hy ⟨a, Ideal.pow_le_pow_right hkl ha⟩
    have hdirA : Directed (· ≤ ·) (fun k : ℕ =>
        (Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup) :=
      hdirS.mono_comp _ (fun _ _ h => Submodule.toAddSubgroup_mono h)
    rw [Submodule.mem_iSup_of_directed _ hdirS]
    change _ ↔ x ∈ (AddMonoidHom.ker ((q ^ m : ℤ) • AddMonoidHom.id (JZero p))) ⊓
      ⨆ k : ℕ, (Submodule.torsionBySet HeckeAlg (JZero p) (↑((eisensteinMaximalIdeal p q) ^ k) : Set HeckeAlg)).toAddSubgroup
    rw [AddSubgroup.mem_inf, AddSubgroup.mem_iSup_of_directed hdirA, AddMonoidHom.mem_ker]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨by simpa using hx, k, hk⟩
    · rintro ⟨-, k, hk⟩
      exact ⟨k, hk⟩
  have hfix : ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
      (t m • x = x ↔ x ∈ eisensteinPrimaryTorsionBar p q m) := fun m x hx => by
    rw [ht2 m x ((hmem m x).mpr hx), hprim m x hx]
  have hidem : ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 → t m • (t m • x) = t m • x :=
    fun m x hx => ht1 m x ((hmem m x).mpr hx)

  have hstab : ∀ (m : ℕ) (r : HeckeAlg) (x : JZero p), (q ^ m : ℤ) • x = 0 → (q ^ m : ℤ) • (r • x) = 0 := by
    intro m r x hx
    exact (hmem m _).mp ((Nq m).smul_mem r ((hmem m x).mpr hx))
  have hup : ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 → (q ^ (m + 1) : ℤ) • x = 0 := by
    intro m x hx
    rw [pow_succ, mul_comm, mul_smul, hx, smul_zero]
  have hprim_up : ∀ (m : ℕ) (x : JZero p), (q ^ m : ℤ) • x = 0 →
      (x ∈ eisensteinPrimaryTorsionBar p q m ↔ x ∈ eisensteinPrimaryTorsionBar p q (m + 1)) := by
    intro m x hx
    rw [← hprim m x hx, ← hprim (m + 1) x (hup m x hx)]
  refine ⟨t, fun m x hx => ⟨hidem m x hx, hfix m x hx, ?_⟩⟩

  have hy : t m • x ∈ eisensteinPrimaryTorsionBar p q (m + 1) := by
    rw [← hprim_up m _ (hstab m _ x hx), ← hfix m _ (hstab m _ x hx)]
    exact hidem m x hx
  have hz : t (m + 1) • x ∈ eisensteinPrimaryTorsionBar p q m := by
    rw [hprim_up m _ (hstab m _ x hx), ← hfix (m + 1) _ (hup m _ (hstab m _ x hx))]
    exact hidem (m + 1) x (hup m x hx)
  have h1 : t (m + 1) • (t m • x) = t m • x := (hfix (m + 1) _ (hup m _ (hstab m _ x hx))).mpr hy
  have h2 : t m • (t (m + 1) • x) = t (m + 1) • x := (hfix m _ (hstab m _ x hx)).mpr hz
  calc t (m + 1) • x = t m • (t (m + 1) • x) := h2.symm
    _ = t (m + 1) • (t m • x) := by rw [← mul_smul, ← mul_smul, mul_comm]
    _ = t m • x := h1

end S_ModularCurve_exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar
end P2MW
export P2MW.S_ModularCurve_exists_heckeAlg_tower_smul_smul_eq_and_smul_eq_iff_mem_eisensteinPrimaryTorsionBar (solution)
