-- Prove2me | solution 1 for ModularForm.heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/028da08a-9cc5-5e9b-bd3c-c9c076d2fbee

import Mathlib
import Definitions.Def_CuspForm_TwoCuspLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div

set_option autoImplicit false

open scoped MatrixGroups ModularForm
open Matrix

namespace FAL

def gam (Q R M q' s a b j j' c : ℤ) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![s * (R * a * b * j' + a - Q * R * a ^ 2 * j * j' - R * a * j - R * a * b * q' * j') - R * b,
      -a * b + Q * a ^ 2 * j + q' * a * b;
    M * c,
      -R * b + R * Q * a * j + Q * q' * a]

theorem identity_real (Q R M q' s a b j j' c : ℤ) (hM : M = Q * R) (hQ : Q = q' * s) (hR : R ≠ 0) (hq' : q' ≠ 0)
    (hbez : Q * a - R * b = 1)
    (hX : R * j' * b + 1 - Q * R * a * j * j' - R * j - Q * q' * a * j' - q' = q' * c) :
    (!![(Q : ℝ) * a, b; M, Q] : Matrix (Fin 2) (Fin 2) ℝ) * !![(1 : ℝ), j; 0, q'] =
      ((gam Q R M q' s a b j j' c).map (Int.castRingHom ℝ)) * (!![(q' : ℝ), 0; 0, 1] * !![(1 : ℝ), 0; M * j', 1]) *
        !![(Q : ℝ) * a, b; M, Q] := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hqr : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]
    have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have hc : (c : ℝ) = ((R : ℝ) * j' * b + 1 - Q * R * a * j * j' - R * j - Q * q' * a * j' - q') / q' := by
    rw [eq_div_iff hqr]
    have := congrArg (fun z : ℤ => (z : ℝ)) hX; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  have hQr : (Q : ℝ) = q' * s := by exact_mod_cast hQ
  simp only [gam, Matrix.map, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, eq_intCast, Int.cast_add, Int.cast_sub, Int.cast_mul, Int.cast_pow,
    Int.cast_neg, Int.cast_one]
  ext i k
  fin_cases i <;> fin_cases k <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    (simp only [hc, hb, hMr, hQr]; field_simp; ring)

theorem det_gam (Q R M q' s a b j j' c : ℤ) (hM : M = Q * R) (hQ : Q = q' * s) (hR : R ≠ 0) (hq' : q' ≠ 0)
    (hbez : Q * a - R * b = 1)
    (hX : R * j' * b + 1 - Q * R * a * j * j' - R * j - Q * q' * a * j' - q' = q' * c) :
    (gam Q R M q' s a b j j' c).det = 1 := by
  have hRr : (R : ℝ) ≠ 0 := by exact_mod_cast hR
  have hqr : (q' : ℝ) ≠ 0 := by exact_mod_cast hq'
  have hb : (b : ℝ) = ((Q : ℝ) * a - 1) / R := by
    rw [eq_div_iff hRr]
    have := congrArg (fun z : ℤ => (z : ℝ)) hbez; push_cast at this; linarith
  have hc : (c : ℝ) = ((R : ℝ) * j' * b + 1 - Q * R * a * j * j' - R * j - Q * q' * a * j' - q') / q' := by
    rw [eq_div_iff hqr]
    have := congrArg (fun z : ℤ => (z : ℝ)) hX; push_cast at this; linarith
  have hMr : (M : ℝ) = Q * R := by exact_mod_cast hM
  have hQr : (Q : ℝ) = q' * s := by exact_mod_cast hQ
  apply Int.cast_injective (α := ℝ)
  rw [gam, Matrix.det_fin_two_of]
  push_cast
  simp only [hc, hb, hMr, hQr]
  field_simp
  ring

end FAL

namespace FAL

theorem val_mapGL_STS (n : ℤ) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-n) * ModularGroup.S⁻¹) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) = !![(1 : ℝ), 0; (n : ℝ), 1] := by
  have h1 : ((ModularGroup.S * ModularGroup.T ^ (-n) * ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) =
      !![(1 : ℤ), 0; n, 1] := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
      ModularGroup.coe_S, ModularGroup.coe_T_zpow, Matrix.adjugate_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
  have h2 : ((Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-n) * ModularGroup.S⁻¹) : GL (Fin 2) ℝ) :
        Matrix (Fin 2) (Fin 2) ℝ) =
      (((ModularGroup.S * ModularGroup.T ^ (-n) * ModularGroup.S⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).map (Int.castRingHom ℝ) :=
    Matrix.ext fun i => congrFun rfl
  rw [h2, h1]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem val_mapGL (g : SL(2, ℤ)) :
    ((Matrix.SpecialLinearGroup.mapGL ℝ g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = (g : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℝ) :=
  Matrix.ext fun i => congrFun rfl

theorem val_alGL {M Q : ℕ} [NeZero M] (W : ModularForm.AtkinLehnerDatum M Q) :
    ((W.alGL : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) = !![(Q : ℝ) * W.a, W.b; M, Q] := by
  rw [ModularForm.AtkinLehnerDatum.alGL_coe, ModularForm.AtkinLehnerDatum.mat]
  have hM : (M : ℝ) = (Q : ℝ) * W.R := by exact_mod_cast W.hM
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hM]

theorem sum_slash {ι : Type*} (s : Finset ι) (k : ℤ) (g : GL (Fin 2) ℝ) (F : ι → UpperHalfPlane → ℂ) :
    (∑ i ∈ s, F i) ∣[k] g = ∑ i ∈ s, (F i) ∣[k] g := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SlashAction.zero_slash]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

end FAL

open FAL in
set_option maxHeartbeats 3200000 in
theorem solution
    (M p : ℕ) [NeZero M] [Fact p.Prime] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ) (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (W : ModularForm.AtkinLehnerDatum M (M / p))
    (q' : ℕ) (hq' : q'.Prime) (hq'Q : q' ∣ M / p) (k : ℤ)
    (f : UpperHalfPlane → ℂ)
    (hf : ∀ γ ∈ (CohCarrier.GammaH M H : Subgroup (GL (Fin 2) ℝ)), f ∣[k] γ = f) :
    ModularForm.heckeU k q' (ModularForm.alSlash W k f) =
      ModularForm.alSlash W k
        (∑ j ∈ Finset.range q',
          f ∣[k] (ModularForm.heckeDiagMatrix q' *
            (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-((M * j : ℕ) : ℤ)) * ModularGroup.S⁻¹) :
              GL (Fin 2) ℝ))) := by
  classical
  let Q : ℕ := M / p
  have hq'0 : q' ≠ 0 := hq'.ne_zero
  have hq'Z0 : (q' : ℤ) ≠ 0 := by exact_mod_cast hq'0
  obtain ⟨s, hs⟩ := hq'Q
  have hQ : (Q : ℤ) = (q' : ℤ) * (s : ℤ) := by exact_mod_cast hs
  have hMZ : (M : ℤ) = (Q : ℤ) * (W.R : ℤ) := by exact_mod_cast W.hM
  have hbez : (Q : ℤ) * W.a - (W.R : ℤ) * W.b = 1 := W.bezout
  have hR0 : (W.R : ℤ) ≠ 0 := by exact_mod_cast W.R_pos.ne'
  haveI : Fact q'.Prime := ⟨hq'⟩

  have hQmod : ((Q : ℕ) : ZMod q') = 0 := by
    show ((M / p : ℕ) : ZMod q') = 0
    rw [hs]; push_cast; rw [ZMod.natCast_self, zero_mul]
  have hq'mod : ((q' : ℕ) : ZMod q') = 0 := ZMod.natCast_self q'
  have hRb : ((W.R : ℕ) : ZMod q') * ((W.b : ℤ) : ZMod q') = -1 := by
    have h := congrArg (fun z : ℤ => (z : ZMod q')) hbez
    push_cast at h
    rw [hQmod] at h
    linear_combination -h
  have hRunit : IsUnit ((W.R : ℕ) : ZMod q') :=
    isUnit_iff_exists_inv.mpr ⟨-((W.b : ℤ) : ZMod q'), by rw [mul_neg, hRb, neg_neg]⟩

  let σ : ℕ → ℕ := fun j => ((1 - (W.R : ℤ) * (j : ℤ)) % (q' : ℤ)).toNat
  have hσZ : ∀ j : ℕ, ((σ j : ℕ) : ℤ) = (1 - (W.R : ℤ) * (j : ℤ)) % (q' : ℤ) := fun j =>
    Int.toNat_of_nonneg (Int.emod_nonneg _ hq'Z0)
  have hσlt : ∀ j, σ j < q' := fun j => by
    have h1 : (1 - (W.R : ℤ) * (j : ℤ)) % (q' : ℤ) < (q' : ℤ) := Int.emod_lt_of_pos _ (by exact_mod_cast hq'.pos)
    have h2 := hσZ j
    omega
  have hσcast : ∀ j : ℕ, ((σ j : ℕ) : ZMod q') = 1 - ((W.R : ℕ) : ZMod q') * ((j : ℕ) : ZMod q') := fun j => by
    have h2 : (((σ j : ℕ) : ℤ) : ZMod q') = (((1 - (W.R : ℤ) * (j : ℤ)) % (q' : ℤ) : ℤ) : ZMod q') := by rw [hσZ j]
    rw [ZMod.intCast_mod] at h2
    push_cast at h2
    exact h2

  have hX : ∀ j : ℕ, (q' : ℤ) ∣ ((W.R : ℤ) * (σ j : ℕ) * W.b + 1 - (Q : ℤ) * W.R * W.a * (j : ℕ) * (σ j : ℕ) - W.R * (j : ℕ) -
      (Q : ℤ) * q' * W.a * (σ j : ℕ) - q') := by
    intro j
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [hσcast j]
    linear_combination (1 - ((W.R : ℕ) : ZMod q') * ((j : ℕ) : ZMod q')) * hRb +
      (-((W.R : ℕ) : ZMod q') * ((W.a : ℤ) : ZMod q') * ((j : ℕ) : ZMod q') * (1 - ((W.R : ℕ) : ZMod q') * ((j : ℕ) : ZMod q')) -
        ((q' : ℕ) : ZMod q') * ((W.a : ℤ) : ZMod q') * (1 - ((W.R : ℕ) : ZMod q') * ((j : ℕ) : ZMod q'))) * hQmod +
      (-1 : ZMod q') * hq'mod
  choose c hc using hX

  have hdet : ∀ j : ℕ, (gam (Q : ℤ) (W.R : ℤ) (M : ℤ) (q' : ℤ) (s : ℤ) W.a W.b (j : ℕ) (σ j : ℕ) (c j)).det = 1 := fun j =>
    det_gam _ _ _ _ _ _ _ _ _ _ hMZ hQ hR0 hq'Z0 hbez (hc j)
  let γSL : ℕ → SL(2, ℤ) := fun j => ⟨gam (Q : ℤ) (W.R : ℤ) (M : ℤ) (q' : ℤ) (s : ℤ) W.a W.b (j : ℕ) (σ j : ℕ) (c j), hdet j⟩
  have hγ10 : ∀ j, ((γSL j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = (M : ℤ) * c j := fun j => rfl
  have hγ11 : ∀ j, ((γSL j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = -(W.R : ℤ) * W.b + W.R * Q * W.a * (j : ℕ) + Q * q' * W.a := fun j => rfl
  have hγmem : ∀ j, γSL j ∈ CohCarrier.GammaH M H := by
    intro j
    rw [CohCarrier.mem_GammaH_iff]
    have hA : γSL j ∈ CongruenceSubgroup.Gamma0 M := by
      rw [CongruenceSubgroup.Gamma0_mem, hγ10]
      push_cast
      rw [ZMod.natCast_self, zero_mul]
    refine ⟨hA, hHp _ ?_⟩
    apply Units.ext
    rw [ZMod.unitsMap_def, Units.coe_map, Units.val_one]
    show ZMod.castHom (Nat.div_dvd_of_dvd hpM) (ZMod Q) ((CongruenceSubgroup.Gamma0Map M) ⟨γSL j, hA⟩) = 1
    have h11 : ((γSL j : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 1 1 = 1 + (Q : ℤ) * (W.R * W.a * (j : ℕ) + q' * W.a - W.a) := by
      rw [hγ11]; linear_combination hbez
    simp only [CongruenceSubgroup.Gamma0Map, MonoidHom.coe_mk, OneHom.coe_mk, h11]
    rw [map_intCast]
    push_cast
    rw [ZMod.natCast_self, zero_mul, add_zero]

  have hGL : ∀ j : ℕ, W.alGL * ModularForm.heckeMatrix q' j =
      (Matrix.SpecialLinearGroup.mapGL ℝ (γSL j) : GL (Fin 2) ℝ) *
        (ModularForm.heckeDiagMatrix q' *
          (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-((M * σ j : ℕ) : ℤ)) * ModularGroup.S⁻¹) : GL (Fin 2) ℝ)) *
        W.alGL := by
    intro j
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, val_alGL, ModularForm.val_heckeMatrix hq'0,
      ModularForm.val_heckeDiagMatrix hq'0, val_mapGL_STS, val_mapGL]
    have h := identity_real (Q : ℤ) (W.R : ℤ) (M : ℤ) (q' : ℤ) (s : ℤ) W.a W.b (j : ℕ) (σ j : ℕ) (c j) hMZ hQ hR0 hq'Z0 hbez (hc j)
    push_cast at h ⊢
    exact h

  have hterm : ∀ j ∈ Finset.range q', (ModularForm.alSlash W k f) ∣[k] ModularForm.heckeMatrix q' j =
      (f ∣[k] (ModularForm.heckeDiagMatrix q' *
        (Matrix.SpecialLinearGroup.mapGL ℝ (ModularGroup.S * ModularGroup.T ^ (-((M * σ j : ℕ) : ℤ)) * ModularGroup.S⁻¹) : GL (Fin 2) ℝ))) ∣[k] W.alGL := by
    intro j _
    rw [ModularForm.alSlash_def, ← SlashAction.slash_mul, hGL j, SlashAction.slash_mul, SlashAction.slash_mul,
      hf _ (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (hγmem j))]
  rw [ModularForm.heckeU_def, Finset.sum_congr rfl hterm, ModularForm.alSlash_def, sum_slash]

  have hmaps : ∀ j ∈ Finset.range q', σ j ∈ Finset.range q' := fun j _ => Finset.mem_range.mpr (hσlt j)
  have hinj : Set.InjOn σ ↑(Finset.range q') := by
    intro j₁ hj₁ j₂ hj₂ h
    have hj₁' : j₁ < q' := Finset.mem_range.mp hj₁
    have hj₂' : j₂ < q' := Finset.mem_range.mp hj₂
    have h1 := hσcast j₁
    have h2 := hσcast j₂
    rw [show σ j₁ = σ j₂ from h] at h1
    rw [h1] at h2

    have h3 : ((W.R : ℕ) : ZMod q') * ((j₁ : ℕ) : ZMod q') = ((W.R : ℕ) : ZMod q') * ((j₂ : ℕ) : ZMod q') := by
      linear_combination -h2
    have h4 : ((j₁ : ℕ) : ZMod q') = ((j₂ : ℕ) : ZMod q') := hRunit.mul_left_cancel h3
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hj₁', Nat.mod_eq_of_lt hj₂'] at h4
    exact h4
  refine Finset.sum_nbij σ hmaps hinj ?_ (fun j _ => rfl)
  exact Finset.surjOn_of_injOn_of_card_le σ (fun j hj => hmaps j hj) hinj le_rfl

end S_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div
end P2MW
export P2MW.S_ModularForm_heckeU_alSlash_eq_alSlash_sum_slash_transpose_of_dvd_div (solution)
