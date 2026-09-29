-- Prove2me | solution 1 for ModularCurve.FullLevel.gl2Laws_of_not_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/b17b18b4-3585-549f-be9a-82c92d0ed8fb

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj
import Theorems.Thm_ModularCurve_surjective_specialLinearGroup_map_zmod
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_gl2Laws_of_not_dvd

open scoped MatrixGroups
open Matrix ModularCurve ModularCurve.FullLevel CongruenceSubgroup

set_option autoImplicit false

noncomputable section

namespace W1GL

variable {q : ℕ} [Fact q.Prime] {M' : ℕ}

section Reduction

abbrev SLq (n : ℕ) : SL(2, ℤ) →* SL(2, ZMod n) :=
  Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod n))

omit [Fact q.Prime] in
theorem SLq_apply (n : ℕ) (g : SL(2, ℤ)) (i j : Fin 2) : (SLq n g) i j = ((g i j : ℤ) : ZMod n) := rfl

omit [Fact q.Prime] in
theorem SLq_eq_iff (n : ℕ) (g g' : SL(2, ℤ)) :
    SLq n g = SLq n g' ↔ ∀ i j, (n : ℤ) ∣ g' i j - g i j := by
  constructor
  · intro h i j
    have hij : (SLq n g) i j = (SLq n g') i j := by rw [h]
    rw [SLq_apply, SLq_apply] at hij
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp hij
  · intro h
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rw [SLq_apply, SLq_apply]
    exact (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mpr (h i j)

omit [Fact q.Prime] in
theorem SLq_eq_one_iff (n : ℕ) (g : SL(2, ℤ)) : SLq n g = 1 ↔ g ∈ Gamma n :=
  (Gamma_mem'.symm)

theorem redQ_eq (γ : SL(2, ℤ)) : redQ q γ = Matrix.SpecialLinearGroup.toGL (SLq q γ) := rfl

theorem map_cast_eq (γ : SL(2, ℤ)) :
    (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) =
      ((SLq q γ : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) := by
  ext i j
  rw [SLq_apply]
  rfl

theorem coe_redQ (γ : SL(2, ℤ)) :
    ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (γ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ZMod q) := by
  rw [map_cast_eq]
  rfl

omit [Fact q.Prime] in

theorem exists_crt {P M₁ : ℕ} [NeZero P] [NeZero M₁] (hcop : Nat.Coprime P M₁) (g : SL(2, ℤ)) :
    ∃ g₁ : SL(2, ℤ), SLq P g₁ = SLq P g ∧ SLq M₁ g₁ = 1 := by
  obtain ⟨x, y, hxy⟩ : IsCoprime (P : ℤ) (M₁ : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  haveI : NeZero (P * M₁) := ⟨mul_ne_zero (NeZero.ne P) (NeZero.ne M₁)⟩
  set n : ℕ := P * M₁ with hn
  set e : ℤ := y * M₁ with he
  set f : ℤ := x * P with hf
  have hef : e + f = 1 := by rw [he, hf]; linear_combination hxy
  have hef' : (n : ℤ) ∣ e * f := ⟨x * y, by rw [hn, he, hf]; push_cast; ring⟩
  have hdet : (g 0 0 : ℤ) * g 1 1 - g 0 1 * g 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe g
    rw [Matrix.det_fin_two] at h
    exact h
  have hE : ((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hef
  have hEF : ((e : ℤ) : ZMod n) * ((f : ℤ) : ZMod n) = 0 := by
    rw [← Int.cast_mul, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hef'
  have hD : ((g 0 0 : ℤ) : ZMod n) * ((g 1 1 : ℤ) : ZMod n)
      - ((g 0 1 : ℤ) : ZMod n) * ((g 1 0 : ℤ) : ZMod n) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → ZMod n) hdet
  let Y : SL(2, ZMod n) :=
    ⟨!![((e * g 0 0 + f : ℤ) : ZMod n), ((e * g 0 1 : ℤ) : ZMod n);
        ((e * g 1 0 : ℤ) : ZMod n), ((e * g 1 1 + f : ℤ) : ZMod n)], by
      rw [Matrix.det_fin_two_of]
      push_cast
      linear_combination ((e : ℤ) : ZMod n) ^ 2 * hD
        + (((g 0 0 : ℤ) : ZMod n) + ((g 1 1 : ℤ) : ZMod n) - 2) * hEF
        + (((e : ℤ) : ZMod n) + ((f : ℤ) : ZMod n) + 1) * hE⟩
  obtain ⟨g₁, hg₁⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod n Y
  have hent : ∀ i j : Fin 2, (SLq n g₁) i j = Y i j := fun i j => by rw [← hg₁]
  have h00 : (n : ℤ) ∣ (e * g 0 0 + f) - g₁ 0 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 0 0)
  have h01 : (n : ℤ) ∣ (e * g 0 1) - g₁ 0 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 0 1)
  have h10 : (n : ℤ) ∣ (e * g 1 0) - g₁ 1 0 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 1 0)
  have h11 : (n : ℤ) ∣ (e * g 1 1 + f) - g₁ 1 1 :=
    (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).mp (by simpa [SLq_apply, Y] using hent 1 1)
  have hPn : (P : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_right _ _
  have hMn : (M₁ : ℤ) ∣ n := by rw [hn]; push_cast; exact dvd_mul_left _ _
  have hPe : (P : ℤ) ∣ e - 1 := ⟨-x, by rw [he]; linear_combination hxy⟩
  have hPf : (P : ℤ) ∣ f := ⟨x, by rw [hf]; ring⟩
  have hMe : (M₁ : ℤ) ∣ e := ⟨y, by rw [he]; ring⟩
  have hMf : (M₁ : ℤ) ∣ f - 1 := ⟨-y, by rw [hf]; linear_combination hxy⟩
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (P : ℤ) ∣ g 0 0 - g₁ 0 0
      have : g 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - (e - 1) * g 0 0 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h00) (dvd_mul_of_dvd_left hPe _)) hPf
    · show (P : ℤ) ∣ g 0 1 - g₁ 0 1
      have : g 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - (e - 1) * g 0 1 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h01) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 0 - g₁ 1 0
      have : g 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - (e - 1) * g 1 0 := by ring
      rw [this]
      exact dvd_sub (dvd_trans hPn h10) (dvd_mul_of_dvd_left hPe _)
    · show (P : ℤ) ∣ g 1 1 - g₁ 1 1
      have : g 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - (e - 1) * g 1 1 - f := by ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hPn h11) (dvd_mul_of_dvd_left hPe _)) hPf
  · rw [← map_one (SLq M₁), SLq_eq_iff]
    intro i j
    fin_cases i <;> fin_cases j
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 0 - g₁ 0 0
      have : (1 : SL(2, ℤ)) 0 0 - g₁ 0 0 = ((e * g 0 0 + f) - g₁ 0 0) - e * g 0 0 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h00) (dvd_mul_of_dvd_left hMe _)) hMf
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 0 1 - g₁ 0 1
      have : (1 : SL(2, ℤ)) 0 1 - g₁ 0 1 = ((e * g 0 1) - g₁ 0 1) - e * g 0 1 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h01) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 0 - g₁ 1 0
      have : (1 : SL(2, ℤ)) 1 0 - g₁ 1 0 = ((e * g 1 0) - g₁ 1 0) - e * g 1 0 := by simp
      rw [this]
      exact dvd_sub (dvd_trans hMn h10) (dvd_mul_of_dvd_left hMe _)
    · show (M₁ : ℤ) ∣ (1 : SL(2, ℤ)) 1 1 - g₁ 1 1
      have : (1 : SL(2, ℤ)) 1 1 - g₁ 1 1 = ((e * g 1 1 + f) - g₁ 1 1) - e * g 1 1 - (f - 1) := by
        simp; ring
      rw [this]
      exact dvd_sub (dvd_sub (dvd_trans hMn h11) (dvd_mul_of_dvd_left hMe _)) hMf

theorem exists_mem_Gamma0_SLq_eq (hqM' : ¬ q ∣ M') (g : SL(2, ZMod q)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ SLq q γ = g := by
  haveI : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  haveI : NeZero M' := ⟨by rintro rfl; exact hqM' (dvd_zero q)⟩
  obtain ⟨g₀, hg₀⟩ := ModularCurve.surjective_specialLinearGroup_map_zmod q g
  obtain ⟨g₁, hg₁q, hg₁M⟩ :=
    exists_crt ((Nat.Prime.coprime_iff_not_dvd (Fact.out : q.Prime)).mpr hqM') g₀
  refine ⟨g₁, ?_, ?_⟩
  · rw [SLq_eq_one_iff, Gamma_mem] at hg₁M
    rw [Gamma0_mem]
    exact hg₁M.2.2.1
  · rw [hg₁q]
    exact hg₀

end Reduction

section IdxArith

theorem pow_val_eq_pow_mod (ζ : Idx q) (n : ℕ) : ζ.val ^ n = ζ.val ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, ζ.isPrimitiveRoot.pow_eq_one, one_pow, one_mul]

theorem Idx.pow_pow (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = ζ.pow (a * b) := by
  apply Idx.ext
  rw [Idx.val_pow, Idx.val_pow, Idx.val_pow, ← pow_mul, Units.val_mul, ZMod.val_mul,
    ← pow_val_eq_pow_mod]

theorem Idx.pow_one (ζ : Idx q) : ζ.pow 1 = ζ := by
  haveI : Fact (1 < q) := ⟨(Fact.out : q.Prime).one_lt⟩
  apply Idx.ext
  rw [Idx.val_pow, Units.val_one, ZMod.val_one, _root_.pow_one]

end IdxArith

section Laws

variable (hqM' : ¬ q ∣ M')
include hqM'

theorem levelAutBar_mul' (ζ : Idx q) {α β : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M') :
    levelAutBar q M' ζ (α * β) = (levelAutBar q M' ζ α).trans (levelAutBar q M' ζ β) :=
  ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ α β hα hβ

theorem levelAutBar_reciprocity (ζ : Idx q) (d : (ZMod q)ˣ) {α α' : SL(2, ℤ)} (hα : α ∈ Gamma0 M')
    (hα' : α' ∈ Gamma0 M') (hGL : diagOneElem q d * redQ q α = redQ q α' * diagOneElem q d) :
    levelAutBar q M' (ζ.pow d⁻¹) α = levelAutBar q M' ζ α' := by
  refine ModularCurve.FullLevel.levelAutBar_pow_inv_eq_levelAutBar_of_diag_conj q M' hqM' ζ d α α' hα hα' ?_
  have := congrArg (fun g : CuspidalType.GL2 q => (g : Matrix (Fin 2) (Fin 2) (ZMod q))) hGL
  simpa only [Matrix.GeneralLinearGroup.coe_mul, coe_diagOneElem, coe_redQ] using this

theorem levelAutBar_congr (ζ : Idx q) {α α' : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hα' : α' ∈ Gamma0 M')
    (h : SLq q α = SLq q α') : levelAutBar q M' ζ α = levelAutBar q M' ζ α' := by
  have key := levelAutBar_reciprocity hqM' ζ 1 hα hα' (by
    have h1 : diagOneElem q 1 = 1 := by
      refine Matrix.GeneralLinearGroup.ext fun i j => ?_
      rw [coe_diagOneElem, Units.val_one]
      fin_cases i <;> fin_cases j <;> rfl
    rw [h1, one_mul, mul_one, redQ_eq, redQ_eq, h])
  rwa [inv_one, Idx.pow_one] at key

theorem levelAutBar_one (ζ : Idx q) : levelAutBar q M' ζ 1 = AlgEquiv.refl := by
  have h := levelAutBar_mul' hqM' ζ (one_mem (Gamma0 M')) (one_mem (Gamma0 M'))
  rw [mul_one, ← AlgEquiv.aut_mul] at h
  have h' : levelAutBar q M' ζ 1 * levelAutBar q M' ζ 1 = levelAutBar q M' ζ 1 * 1 := by
    rw [mul_one]; exact h.symm
  rw [← AlgEquiv.aut_one]
  exact mul_left_cancel h'

theorem levelAutBar_of_SLq_eq_one (ζ : Idx q) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (h1 : SLq q γ = 1) :
    levelAutBar q M' ζ γ = AlgEquiv.refl := by
  rw [levelAutBar_congr hqM' ζ hγ (one_mem _) (by rw [h1, map_one]), levelAutBar_one hqM']

omit hqM' in

abbrev slE (γ : SL(2, ℤ)) : AddMonoid.End (Jac q M') := slJac q M' γ

omit hqM' in

abbrev dgE (d : (ZMod q)ˣ) : AddMonoid.End (Jac q M') := diagJac q M' d

theorem levelOp_mul (ζ : Idx q) {α β : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M')
    (x : jacComp q M') : levelOp q M' ζ (α * β) x = levelOp q M' ζ β (levelOp q M' ζ α x) := by
  rw [levelOp_apply, levelOp_apply, levelOp_apply, levelAutBar_mul' hqM' ζ hα hβ, ← AlgEquiv.aut_mul,
    map_mul, mul_smul]

theorem levelOp_of_SLq_eq_one (ζ : Idx q) {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (h1 : SLq q γ = 1)
    (x : jacComp q M') : levelOp q M' ζ γ x = x := by
  rw [levelOp_apply, levelAutBar_of_SLq_eq_one hqM' ζ hγ h1, ← AlgEquiv.aut_one, map_one, one_smul]

theorem levelOp_congr (ζ : Idx q) {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (h : SLq q γ = SLq q γ') (x : jacComp q M') : levelOp q M' ζ γ x = levelOp q M' ζ γ' x := by
  rw [levelOp_apply, levelOp_apply, levelAutBar_congr hqM' ζ hγ hγ' h]

theorem levelOp_reciprocity (ζ : Idx q) (d : (ZMod q)ˣ) {α α' : SL(2, ℤ)} (hα : α ∈ Gamma0 M')
    (hα' : α' ∈ Gamma0 M') (hGL : diagOneElem q d * redQ q α = redQ q α' * diagOneElem q d)
    (x : jacComp q M') : levelOp q M' (ζ.pow d⁻¹) α x = levelOp q M' ζ α' x := by
  rw [levelOp_apply, levelOp_apply, levelAutBar_reciprocity hqM' ζ d hα hα' hGL]

theorem slE_mul {α β : SL(2, ℤ)} (hα : α ∈ Gamma0 M') (hβ : β ∈ Gamma0 M') :
    (slE (α * β) : AddMonoid.End (Jac q M')) = slE α * slE β := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (slJac q M' (α * β) x).eval ζ = (slJac q M' α (slJac q M' β x)).eval ζ
  rw [slJac_eval, slJac_eval, slJac_eval, _root_.mul_inv_rev, levelOp_mul hqM' ζ (inv_mem hβ) (inv_mem hα)]

theorem slE_of_SLq_eq_one {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (h1 : SLq q γ = 1) :
    (slE γ : AddMonoid.End (Jac q M')) = 1 := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (slJac q M' γ x).eval ζ = x.eval ζ
  rw [slJac_eval, levelOp_of_SLq_eq_one hqM' ζ (inv_mem hγ) (by rw [map_inv, h1, inv_one])]

theorem slE_congr {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M') (h : SLq q γ = SLq q γ') :
    (slE γ : AddMonoid.End (Jac q M')) = slE γ' := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (slJac q M' γ x).eval ζ = (slJac q M' γ' x).eval ζ
  rw [slJac_eval, slJac_eval, levelOp_congr hqM' ζ (inv_mem hγ) (inv_mem hγ') (by rw [map_inv, map_inv, h])]

omit hqM' in
theorem dgE_mul (d₁ d₂ : (ZMod q)ˣ) : (dgE (d₁ * d₂) : AddMonoid.End (Jac q M')) = dgE d₁ * dgE d₂ := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (diagJac q M' (d₁ * d₂) x).eval ζ = (diagJac q M' d₁ (diagJac q M' d₂ x)).eval ζ
  simp only [diagJac_eval, Idx.pow_pow, mul_inv]

omit hqM' in
theorem dgE_one : (dgE 1 : AddMonoid.End (Jac q M')) = 1 := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (diagJac q M' 1 x).eval ζ = x.eval ζ
  rw [diagJac_eval, inv_one, Idx.pow_one]

theorem dgE_mul_slE (d : (ZMod q)ˣ) {γ γ' : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') (hγ' : γ' ∈ Gamma0 M')
    (hGL : diagOneElem q d * redQ q γ = redQ q γ' * diagOneElem q d) :
    (dgE d : AddMonoid.End (Jac q M')) * slE γ = slE γ' * dgE d := by
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (diagJac q M' d (slJac q M' γ x)).eval ζ = (slJac q M' γ' (diagJac q M' d x)).eval ζ
  rw [diagJac_eval, slJac_eval, slJac_eval, diagJac_eval]
  refine levelOp_reciprocity hqM' ζ d (inv_mem hγ) (inv_mem hγ') ?_ _
  rw [map_inv, map_inv]
  calc diagOneElem q d * (redQ q γ)⁻¹
      = (redQ q γ')⁻¹ * (redQ q γ' * diagOneElem q d) * (redQ q γ)⁻¹ := by group
    _ = (redQ q γ')⁻¹ * (diagOneElem q d * redQ q γ) * (redQ q γ)⁻¹ := by rw [hGL]
    _ = (redQ q γ')⁻¹ * diagOneElem q d := by group

def sec (g : SL(2, ZMod q)) : SL(2, ℤ) := (exists_mem_Gamma0_SLq_eq (M' := M') hqM' g).choose

theorem sec_mem (g : SL(2, ZMod q)) : sec (M' := M') hqM' g ∈ Gamma0 M' :=
  (exists_mem_Gamma0_SLq_eq (M' := M') hqM' g).choose_spec.1

theorem SLq_sec (g : SL(2, ZMod q)) : SLq q (sec (M' := M') hqM' g) = g :=
  (exists_mem_Gamma0_SLq_eq (M' := M') hqM' g).choose_spec.2

def S (g : SL(2, ZMod q)) : AddMonoid.End (Jac q M') := slE (sec (M' := M') hqM' g)

theorem S_SLq {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') : S (M' := M') hqM' (SLq q γ) = slE γ :=
  slE_congr hqM' (sec_mem hqM' _) hγ (SLq_sec hqM' _)

theorem S_one : S (M' := M') hqM' 1 = 1 :=
  slE_of_SLq_eq_one hqM' (sec_mem hqM' _) (SLq_sec hqM' _)

theorem S_mul (g₁ g₂ : SL(2, ZMod q)) : S (M' := M') hqM' (g₁ * g₂) = S hqM' g₁ * S hqM' g₂ := by
  rw [S, S, S, ← slE_mul hqM' (sec_mem hqM' _) (sec_mem hqM' _)]
  exact slE_congr hqM' (sec_mem hqM' _) (mul_mem (sec_mem hqM' _) (sec_mem hqM' _))
    (by rw [SLq_sec, map_mul, SLq_sec, SLq_sec])

omit hqM' in
theorem units_inv_mul_val (d : (ZMod q)ˣ) : ((d⁻¹ : (ZMod q)ˣ) : ZMod q) * (d : ZMod q) = 1 := by
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

omit hqM' in
theorem units_mul_inv_val (d : (ZMod q)ˣ) : (d : ZMod q) * ((d⁻¹ : (ZMod q)ˣ) : ZMod q) = 1 := by
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

omit hqM' in

theorem diag_inv_mul_diag (u : (ZMod q)ˣ) :
    !![(1 : ZMod q), 0; 0, ((u⁻¹ : (ZMod q)ˣ) : ZMod q)] * !![1, 0; 0, (u : ZMod q)] = 1 := by
  rw [Matrix.mul_fin_two, Matrix.one_fin_two]
  simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul, units_inv_mul_val]

def conjSL (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) : SL(2, ZMod q) :=
  ⟨!![s 0 0, s 0 1 * ((d⁻¹ : (ZMod q)ˣ) : ZMod q); (d : ZMod q) * s 1 0, s 1 1], by
    have hdet := Matrix.SpecialLinearGroup.det_coe s
    rw [Matrix.det_fin_two] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet - (s 0 1 * s 1 0) * units_inv_mul_val d⟩

omit hqM' in
theorem coe_conjSL (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) :
    ((conjSL d s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![s 0 0, s 0 1 * ((d⁻¹ : (ZMod q)ˣ) : ZMod q); (d : ZMod q) * s 1 0, s 1 1] :=
  rfl

omit hqM' in
theorem toGL_conjSL_mul (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) :
    Matrix.SpecialLinearGroup.toGL (conjSL d s) * diagOneElem q d =
      diagOneElem q d * Matrix.SpecialLinearGroup.toGL s := by
  apply Units.ext
  change ((conjSL d s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (d : ZMod q)] =
    !![1, 0; 0, (d : ZMod q)] * ((s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))
  conv_rhs => rw [Matrix.eta_fin_two ((s : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q))]
  rw [coe_conjSL, Matrix.mul_fin_two, Matrix.mul_fin_two]
  simp only [mul_one, mul_zero, add_zero, zero_add, one_mul, zero_mul, mul_assoc, units_inv_mul_val]
  rw [mul_comm (s 1 1)]

theorem dgE_mul_S (d : (ZMod q)ˣ) (s : SL(2, ZMod q)) :
    (dgE d : AddMonoid.End (Jac q M')) * S hqM' s = S hqM' (conjSL d s) * dgE d := by
  refine dgE_mul_slE hqM' d (sec_mem hqM' s) (sec_mem hqM' (conjSL d s)) ?_
  rw [redQ_eq, redQ_eq, SLq_sec, SLq_sec]
  exact (toGL_conjSL_mul d s).symm

abbrev detU (g : CuspidalType.GL2 q) : (ZMod q)ˣ := Matrix.GeneralLinearGroup.det g

def slPart (g : CuspidalType.GL2 q) : SL(2, ZMod q) :=
  ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)], by
    rw [Matrix.det_mul, Matrix.det_fin_two_of, ← Matrix.GeneralLinearGroup.val_det_apply, one_mul, mul_zero,
      sub_zero]
    exact units_mul_inv_val (detU g)⟩

omit hqM' in
theorem coe_slPart (g : CuspidalType.GL2 q) :
    ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, (((detU g)⁻¹ : (ZMod q)ˣ) : ZMod q)] :=
  rfl

omit hqM' in
theorem toGL_slPart_mul (g : CuspidalType.GL2 q) :
    Matrix.SpecialLinearGroup.toGL (slPart g) * diagOneElem q (detU g) = g := by
  apply Units.ext
  change ((slPart g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) * !![1, 0; 0, ((detU g : (ZMod q)ˣ) : ZMod q)] =
    (g : Matrix (Fin 2) (Fin 2) (ZMod q))
  rw [coe_slPart, Matrix.mul_assoc, diag_inv_mul_diag, Matrix.mul_one]

omit hqM' in
theorem slPart_eq {g : CuspidalType.GL2 q} {s : SL(2, ZMod q)}
    (hs : Matrix.SpecialLinearGroup.toGL s * diagOneElem q (detU g) = g) : slPart g = s :=
  Matrix.SpecialLinearGroup.toGL_injective (mul_right_cancel ((toGL_slPart_mul g).trans hs.symm))

omit hqM' in
theorem diagOneElem_mul (d₁ d₂ : (ZMod q)ˣ) : diagOneElem q (d₁ * d₂) = diagOneElem q d₁ * diagOneElem q d₂ := by
  apply Units.ext
  change (!![1, 0; 0, ((d₁ * d₂ : (ZMod q)ˣ) : ZMod q)] : Matrix (Fin 2) (Fin 2) (ZMod q)) =
    !![1, 0; 0, (d₁ : ZMod q)] * !![1, 0; 0, (d₂ : ZMod q)]
  rw [Matrix.mul_fin_two, Units.val_mul]
  simp only [mul_one, mul_zero, add_zero, zero_add, zero_mul]

omit hqM' in
theorem diagOneElem_one : diagOneElem q 1 = 1 := by
  refine Matrix.GeneralLinearGroup.ext fun i j => ?_
  rw [coe_diagOneElem, Units.val_one]
  fin_cases i <;> fin_cases j <;> rfl

omit hqM' in
theorem detU_mul (g₁ g₂ : CuspidalType.GL2 q) : detU (g₁ * g₂) = detU g₁ * detU g₂ := map_mul _ _ _

omit hqM' in
theorem detU_one : detU (1 : CuspidalType.GL2 q) = 1 := map_one _

omit hqM' in

theorem slPart_mul (g₁ g₂ : CuspidalType.GL2 q) :
    slPart (g₁ * g₂) = slPart g₁ * conjSL (detU g₁) (slPart g₂) := by
  apply slPart_eq
  rw [map_mul, detU_mul, diagOneElem_mul]
  calc Matrix.SpecialLinearGroup.toGL (slPart g₁) * Matrix.SpecialLinearGroup.toGL (conjSL (detU g₁) (slPart g₂)) *
        (diagOneElem q (detU g₁) * diagOneElem q (detU g₂))
      = Matrix.SpecialLinearGroup.toGL (slPart g₁) *
          (Matrix.SpecialLinearGroup.toGL (conjSL (detU g₁) (slPart g₂)) * diagOneElem q (detU g₁)) *
          diagOneElem q (detU g₂) := by simp only [mul_assoc]
    _ = Matrix.SpecialLinearGroup.toGL (slPart g₁) *
          (diagOneElem q (detU g₁) * Matrix.SpecialLinearGroup.toGL (slPart g₂)) * diagOneElem q (detU g₂) := by
        rw [toGL_conjSL_mul]
    _ = (Matrix.SpecialLinearGroup.toGL (slPart g₁) * diagOneElem q (detU g₁)) *
          (Matrix.SpecialLinearGroup.toGL (slPart g₂) * diagOneElem q (detU g₂)) := by simp only [mul_assoc]
    _ = g₁ * g₂ := by rw [toGL_slPart_mul, toGL_slPart_mul]

def Gfun (g : CuspidalType.GL2 q) : AddMonoid.End (Jac q M') := S hqM' (slPart g) * dgE (detU g)

theorem Gfun_one : Gfun (M' := M') hqM' 1 = 1 := by
  rw [Gfun, slPart_eq (s := 1) (by rw [map_one, one_mul, detU_one, diagOneElem_one]), S_one, one_mul, detU_one,
    dgE_one]

theorem Gfun_mul (g₁ g₂ : CuspidalType.GL2 q) : Gfun (M' := M') hqM' (g₁ * g₂) = Gfun hqM' g₁ * Gfun hqM' g₂ := by
  rw [Gfun, Gfun, Gfun, slPart_mul, S_mul, detU_mul, dgE_mul]
  calc S hqM' (slPart g₁) * S hqM' (conjSL (detU g₁) (slPart g₂)) * ((dgE (detU g₁) : AddMonoid.End (Jac q M')) * dgE (detU g₂))
      = S hqM' (slPart g₁) * (S hqM' (conjSL (detU g₁) (slPart g₂)) * dgE (detU g₁)) * dgE (detU g₂) := by
        simp only [mul_assoc]
    _ = S hqM' (slPart g₁) * (dgE (detU g₁) * S hqM' (slPart g₂)) * dgE (detU g₂) := by
        rw [← dgE_mul_S]
    _ = S hqM' (slPart g₁) * dgE (detU g₁) * (S hqM' (slPart g₂) * dgE (detU g₂)) := by
        simp only [mul_assoc]

def G : CuspidalType.GL2 q →* AddMonoid.End (Jac q M') where
  toFun := Gfun hqM'
  map_one' := Gfun_one hqM'
  map_mul' := Gfun_mul hqM'

theorem G_redQ {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M') : G (M' := M') hqM' (redQ q γ) = slE γ := by
  show Gfun hqM' (redQ q γ) = slE γ
  have hdet : detU (redQ q γ) = 1 := by
    rw [redQ_eq]; exact Matrix.SpecialLinearGroup.coeToGL_det _
  rw [Gfun, slPart_eq (s := SLq q γ) (by rw [hdet, diagOneElem_one, mul_one]; rfl), S_SLq hqM' hγ, hdet,
    dgE_one, mul_one]

theorem G_diagOneElem (d : (ZMod q)ˣ) : G (M' := M') hqM' (diagOneElem q d) = dgE d := by
  show Gfun hqM' (diagOneElem q d) = dgE d
  have hdet : detU (diagOneElem q d) = d := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, coe_diagOneElem, Matrix.det_fin_two_of]
    ring
  rw [Gfun, slPart_eq (s := 1) (by rw [map_one, one_mul, hdet]), S_one, one_mul, hdet]

theorem gl2Laws : GL2Laws q M' :=
  ⟨G hqM', fun _ hγ => G_redQ hqM' hγ, fun d => G_diagOneElem hqM' d⟩

end Laws

end W1GL

end

theorem solution (q : ℕ) [Fact q.Prime] (M' : ℕ) (hqM' : ¬ q ∣ M') :
    ModularCurve.FullLevel.GL2Laws q M' :=
  W1GL.gl2Laws hqM'

end S_ModularCurve_FullLevel_gl2Laws_of_not_dvd
end P2MW
export P2MW.S_ModularCurve_FullLevel_gl2Laws_of_not_dvd (solution)
