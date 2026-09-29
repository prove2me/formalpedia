-- Prove2me | solution 1 for ModularForm.exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/0be613ef-a37b-5215-b4bc-7855c1682b3d

import Mathlib
import Definitions.Def_PeriodPair_Uniformization
import Theorems.Thm_PeriodPair_lattice_eq_of_g2_eq_of_g3_eq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne

set_option autoImplicit false

noncomputable section

p2m_open "UpperHalfPlane ModularForm P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.ModularForm EisensteinSeries Complex"
open scoped MatrixGroups Real Topology Pointwise

namespace ModularForm
p2m_export "ModularForm" "translate slash_apply E coe_mul holo' discriminant_eq_E₄_cube_sub_E₆_sq ext bdd_at_cusps' E₄ mcast E₆ discriminant_ne_zero coe_mcast mul coe_translate"
namespace Gamma0Separation
p2m_open "ModularForm"

def restrict {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k) (h : Γ' ≤ Γ) :
    ModularForm Γ' k where
  toFun := f
  slash_action_eq' A hA := by
    simpa using f.slash_action_eq' A (h hA)
  holo' := f.holo'
  bdd_at_cusps' hc := f.bdd_at_cusps' (hc.mono h)

@[scoped simp] lemma restrict_apply {Γ Γ' : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} (f : ModularForm Γ k)
    (h : Γ' ≤ Γ) (τ : ℍ) : restrict f h τ = f τ := rfl

variable (N : ℕ) [NeZero N]

def gN : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(N : ℝ), 0; 0, 1]
    (by rw [Matrix.det_fin_two_of]; simp [NeZero.ne N])

@[scoped simp] lemma gN_apply (i j : Fin 2) :
    (gN N : Matrix (Fin 2) (Fin 2) ℝ) i j = !![(N : ℝ), 0; 0, 1] i j := rfl

lemma gN_det : (gN N).det.val = N := by
  simp [Matrix.GeneralLinearGroup.val_det_apply, gN, Matrix.det_fin_two_of]

lemma gN_det_pos : 0 < (gN N).det.val := by
  rw [gN_det]; exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)

omit [NeZero N] in

lemma gamma0_le_SL :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤ 𝒮ℒ :=
  Subgroup.map_le_range _ _

lemma gamma0_le_conj :
    ((CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)) ≤
      ConjAct.toConjAct (gN N)⁻¹ • 𝒮ℒ := by
  rintro x ⟨γ, hγ, rfl⟩
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem, map_inv, inv_inv, ConjAct.toConjAct_smul]
  have hγ' : (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N) * N := by
    rw [SetLike.mem_coe, CongruenceSubgroup.Gamma0_mem,
      ZMod.intCast_zmod_eq_zero_iff_dvd] at hγ
    exact (Int.ediv_mul_cancel hγ).symm
  set e : ℤ := (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 / N with he
  have hdet : Matrix.det !![(γ : Matrix (Fin 2) (Fin 2) ℤ) 0 0,
      N * (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1; e, (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1] = 1 := by
    have := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two, hγ'] at this
    rw [Matrix.det_fin_two_of]
    linear_combination this
  refine ⟨⟨_, hdet⟩, ?_⟩
  rw [eq_mul_inv_iff_mul_eq]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, hγ', mul_comm]

def liftN {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k :=
  restrict (ModularForm.translate f (gN N)) (gamma0_le_conj N)

def mulN (τ : ℍ) : ℍ := gN N • τ

@[scoped simp] lemma coe_mulN (τ : ℍ) : ((mulN N τ : ℍ) : ℂ) = N * τ := by
  rw [mulN, coe_smul_of_det_pos (gN_det_pos N), num, denom]
  simp

lemma liftN_apply {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) :
    liftN N f τ = (N : ℂ) ^ (k - 1) * f (mulN N τ) := by
  rw [liftN, restrict_apply, ModularForm.coe_translate, ModularForm.slash_apply, σ,
    if_pos (gN_det_pos N), gN_det, denom]
  simp [mulN, mul_comm]

def res {k : ℤ} (f : ModularForm 𝒮ℒ k) :
    ModularForm (CongruenceSubgroup.Gamma0 N : Subgroup SL(2, ℤ)) k :=
  restrict f (gamma0_le_SL N)

omit [NeZero N] in
@[scoped simp] lemma res_apply {k : ℤ} (f : ModularForm 𝒮ℒ k) (τ : ℍ) : res N f τ = f τ := rfl

private lemma pow_four_six_of_sq {t x : ℂ} (h : t ^ 2 = x) : t ^ 4 = x ^ 2 ∧ t ^ 6 = x ^ 3 := by
  constructor <;> [rw [show (4:ℕ) = 2 * 2 from rfl]; rw [show (6:ℕ) = 2 * 3 from rfl]] <;>
    rw [pow_mul, h]

theorem exists_scalar {a₁ b₁ p₁ q₁ a₂ b₂ p₂ q₂ : ℂ}
    (h₁ : a₁ ^ 3 - b₁ ^ 2 ≠ 0) (h₂ : a₂ ^ 3 - b₂ ^ 2 ≠ 0)
    (R1 : a₁ ^ 3 * b₂ ^ 2 = a₂ ^ 3 * b₁ ^ 2)
    (R2 : a₁ * p₂ = a₂ * p₁)
    (R3 : b₁ * q₂ = b₂ * q₁)
    (R4 : a₁ ^ 3 * q₂ ^ 2 = a₂ ^ 3 * q₁ ^ 2)
    (R5 : b₁ ^ 2 * p₂ ^ 3 = b₂ ^ 2 * p₁ ^ 3) :
    ∃ w : ℂ, w ≠ 0 ∧ a₂ = w ^ 4 * a₁ ∧ b₂ = w ^ 6 * b₁ ∧ p₂ = w ^ 4 * p₁ ∧ q₂ = w ^ 6 * q₁ := by
  by_cases ha₁ : a₁ = 0
  ·
    subst ha₁
    have hb₁ : b₁ ≠ 0 := by rintro rfl; exact h₁ (by ring)
    have ha₂ : a₂ = 0 := by
      have : a₂ ^ 3 * b₁ ^ 2 = 0 := by rw [← R1]; ring
      simpa [hb₁] using this
    subst ha₂
    have hb₂ : b₂ ≠ 0 := by rintro rfl; exact h₂ (by ring)
    obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (b₂ / b₁) (by norm_num : 0 < 6)
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff] at ht
      exact ht.elim hb₂ hb₁
    have hb : b₂ = t ^ 6 * b₁ := by rw [ht]; field_simp
    have hq : q₂ = t ^ 6 * q₁ := by
      apply mul_left_cancel₀ hb₁
      rw [R3, hb]; ring

    have hp3 : p₂ ^ 3 = (t ^ 4 * p₁) ^ 3 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hb₁)
      rw [R5, hb]; ring
    by_cases hp₁ : p₁ = 0
    · subst hp₁
      have hp₂ : p₂ = 0 := by simpa using hp3
      exact ⟨t, ht0, by simp, hb, by simp [hp₂], hq⟩
    ·
      set ζ : ℂ := p₂ / (t ^ 4 * p₁) with hζ
      have hζ3 : ζ ^ 3 = 1 := by
        rw [hζ, div_pow, hp3, div_self]
        exact pow_ne_zero _ (mul_ne_zero (pow_ne_zero _ ht0) hp₁)
      have hζ0 : ζ ≠ 0 := by rintro h0; rw [h0] at hζ3; norm_num at hζ3
      refine ⟨ζ * t, mul_ne_zero hζ0 ht0, by simp, ?_, ?_, ?_⟩
      · rw [mul_pow, show ζ ^ 6 = (ζ ^ 3) ^ 2 by ring, hζ3, one_pow, one_mul, hb]
      · rw [mul_pow, show ζ ^ 4 = ζ ^ 3 * ζ by ring, hζ3, one_mul, hζ]
        field_simp
      · rw [mul_pow, show ζ ^ 6 = (ζ ^ 3) ^ 2 by ring, hζ3, one_pow, one_mul, hq]
  ·
    have ha₂ : a₂ ≠ 0 := by
      intro ha₂; subst ha₂
      have hb₂ : b₂ = 0 := by
        have : a₁ ^ 3 * b₂ ^ 2 = 0 := by rw [R1]; ring
        simpa [ha₁] using this
      exact h₂ (by rw [hb₂]; ring)
    have hp : ∀ w : ℂ, a₂ = w ^ 4 * a₁ → p₂ = w ^ 4 * p₁ := by
      intro w hw
      apply mul_left_cancel₀ ha₁
      rw [R2, hw]; ring
    by_cases hb₁ : b₁ = 0
    · subst hb₁
      have hb₂ : b₂ = 0 := by
        have : a₁ ^ 3 * b₂ ^ 2 = 0 := by rw [R1]; ring
        simpa [ha₁] using this
      subst hb₂
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a₂ / a₁) (by norm_num : 0 < 4)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff] at ht
        exact ht.elim ha₂ ha₁
      have ha : a₂ = t ^ 4 * a₁ := by rw [ht]; field_simp

      have hq2 : q₂ ^ 2 = (t ^ 6 * q₁) ^ 2 := by
        apply mul_left_cancel₀ (pow_ne_zero 3 ha₁)
        rw [R4, ha]; ring
      rcases sq_eq_sq_iff_eq_or_eq_neg.1 hq2 with hq | hq
      · exact ⟨t, ht0, ha, by simp, hp t ha, hq⟩
      · have hI4 : Complex.I ^ 4 = 1 := by
          rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, Complex.I_sq]; norm_num
        have hI6 : Complex.I ^ 6 = -1 := by
          rw [show (6:ℕ) = 2 * 3 from rfl, pow_mul, Complex.I_sq]; norm_num
        have ha' : a₂ = (Complex.I * t) ^ 4 * a₁ := by rw [mul_pow, hI4, one_mul]; exact ha
        refine ⟨Complex.I * t, mul_ne_zero Complex.I_ne_zero ht0, ha', by simp, hp _ ha', ?_⟩
        rw [mul_pow, hI6, hq]; ring
    · have hb₂ : b₂ ≠ 0 := by
        intro hb₂
        have : a₂ ^ 3 * b₁ ^ 2 = 0 := by rw [← R1, hb₂]; ring
        simp [ha₂, hb₁] at this
      obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a₁ * b₂ / (a₂ * b₁)) (by norm_num : 0 < 2)
      have ht0 : t ≠ 0 := by
        rintro rfl
        rw [zero_pow (by norm_num), eq_comm, div_eq_zero_iff, mul_eq_zero, mul_eq_zero] at ht
        rcases ht with (h | h) | (h | h) <;> contradiction
      obtain ⟨ht4, ht6⟩ := pow_four_six_of_sq ht
      have ha : a₂ = t ^ 4 * a₁ := by
        rw [ht4, div_pow, div_mul_eq_mul_div,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero ha₂ hb₁))]
        linear_combination -R1
      have hb : b₂ = t ^ 6 * b₁ := by
        rw [ht6, div_pow, div_mul_eq_mul_div,
          eq_div_iff (pow_ne_zero _ (mul_ne_zero ha₂ hb₁))]
        linear_combination -(b₁ * b₂) * R1
      refine ⟨t, ht0, ha, hb, hp t ha, ?_⟩
      apply mul_left_cancel₀ hb₁
      rw [R3, hb]; ring

lemma int_indep (τ : ℍ) {m n m' n' : ℤ}
    (h : (m : ℂ) * τ + n = m' * τ + n') : m = m' ∧ n = n' := by
  have him := congrArg Complex.im h
  simp only [add_im, mul_im, intCast_re, intCast_im, zero_mul, add_zero, coe_im,
    coe_re] at him
  have hm : m = m' := by
    have : ((m : ℝ) - m') * τ.im = 0 := by linarith
    rcases mul_eq_zero.1 this with h0 | h0
    · exact_mod_cast sub_eq_zero.1 h0
    · exact absurd h0 τ.im_pos.ne'
  subst hm
  refine ⟨rfl, ?_⟩
  have := add_left_cancel h
  exact_mod_cast this

theorem exists_gamma0_of_lattice_rel (N : ℕ) (τ₁ τ₂ : ℍ) {u : ℂ} (hu : u ≠ 0)
    {a b c d p q r s e f : ℤ}
    (h1 : u * (a * τ₁ + b) = τ₂) (h2 : u * (c * τ₁ + d) = 1)
    (h3 : p * (τ₂ : ℂ) + q = u * τ₁) (h4 : r * (τ₂ : ℂ) + s = u)
    (h5 : u * (e * (N * τ₁) + f) = 1) :
    ∃ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ₁ = τ₂ := by

  have hcd : c = e * N ∧ d = f := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    rw [h2, ← h5]; push_cast; ring

  have hrow₁ : p * a + q * c = 1 ∧ p * b + q * d = 0 := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    push_cast
    linear_combination p * h1 + q * h2 + h3
  have hrow₂ : r * a + s * c = 0 ∧ r * b + s * d = 1 := by
    refine int_indep τ₁ (mul_left_cancel₀ hu ?_)
    push_cast
    linear_combination r * h1 + s * h2 + h4
  have hdet : (a * d - b * c) * (p * s - q * r) = 1 := by
    linear_combination (r * b + s * d) * hrow₁.1 - (r * a + s * c) * hrow₁.2 + hrow₂.2

  have hz : (c : ℂ) * τ₁ + d ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h2; exact zero_ne_one h2
  have hτ₂ : (τ₂ : ℂ) * (c * τ₁ + d) = a * τ₁ + b := by
    linear_combination -((c : ℂ) * τ₁ + d) * h1 + ((a : ℂ) * τ₁ + b) * h2
  have him : τ₂.im * Complex.normSq (c * τ₁ + d) = (a * d - b * c) * τ₁.im := by
    have h := congrArg Complex.im
      (show (τ₂ : ℂ) * (Complex.normSq ((c : ℂ) * τ₁ + d) : ℂ) =
          (a * τ₁ + b) * (starRingEnd ℂ) (c * τ₁ + d) by
        rw [← Complex.mul_conj, ← mul_assoc, hτ₂])
    simp only [mul_im, ofReal_re, ofReal_im, mul_zero, add_zero, add_im, add_re, mul_re,
      intCast_re, intCast_im, zero_mul, sub_zero, Complex.conj_re, Complex.conj_im, coe_re,
      coe_im] at h
    rw [zero_add] at h
    rw [h]
    ring
  have hdet1 : a * d - b * c = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hdet with h | h
    · exact h
    · exfalso
      have hpos : 0 < τ₂.im * Complex.normSq (c * τ₁ + d) :=
        mul_pos τ₂.im_pos (Complex.normSq_pos.2 hz)
      rw [him] at hpos
      have : ((a * d - b * c : ℤ) : ℝ) = -1 := by exact_mod_cast h
      push_cast at this
      rw [this] at hpos
      linarith [τ₁.im_pos]

  let γ : SL(2, ℤ) := ⟨!![a, b; c, d], by rw [Matrix.det_fin_two_of]; linarith⟩
  refine ⟨⟨γ, ?_⟩, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    simp [γ, hcd.1]
  · apply UpperHalfPlane.ext
    rw [coe_specialLinearGroup_apply]
    simp only [γ, algebraMap_int_eq, eq_intCast, ofReal_intCast, Matrix.of_apply,
      Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      Matrix.empty_val']
    rw [div_eq_iff hz, hτ₂]

section Bridge
open PeriodPair

theorem G_ofTau_eq {k : ℕ} (hk : 3 ≤ k) (τ : ℍ) :
    (ofTau τ).G k = 2 * riemannZeta k * ModularForm.E hk τ := by
  rw [PeriodPair.G, ← (ofTau τ).latticeEquivProd.symm.toEquiv.tsum_eq]
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, ofTau_ω₁, ofTau_ω₂, mul_one]
  have hstep : ∀ p : ℤ × ℤ,
      ((↑p.1 * (τ : ℂ) + ↑p.2) ^ k)⁻¹ = eisSummand k ((finTwoArrowEquiv ℤ).symm p) τ := by
    intro p
    simp only [eisSummand, finTwoArrowEquiv_symm_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_fin_one, zpow_neg, zpow_natCast]
  simp only [hstep]
  rw [(finTwoArrowEquiv ℤ).symm.tsum_eq (f := fun v => eisSummand (k : ℤ) v τ),
    tsum_eisSummand_eq_riemannZeta_mul_eisensteinSeries hk τ,
    show E hk τ = (1 / 2 : ℂ) • eisensteinSeriesSIF (N := 1) 0 k τ from rfl,
    eisensteinSeriesSIF_apply, smul_eq_mul]
  ring

theorem G_scale (L : PeriodPair) (α : ℂˣ) (k : ℕ) :
    (L.scale α).G k = ((α : ℂ) ^ k)⁻¹ * L.G k := by
  rw [PeriodPair.G, PeriodPair.G, ← (L.scale α).latticeEquivProd.symm.toEquiv.tsum_eq,
    ← L.latticeEquivProd.symm.toEquiv.tsum_eq, ← tsum_mul_left]
  congr 1 with p
  simp only [LinearEquiv.coe_toEquiv, latticeEquiv_symm_apply, scale_ω₁, scale_ω₂]
  rw [show (p.1 : ℂ) * (α * L.ω₁) + p.2 * (α * L.ω₂) = α * (p.1 * L.ω₁ + p.2 * L.ω₂) by ring,
    mul_pow, mul_inv]

theorem g₂_scale (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₂ = ((α : ℂ) ^ 4)⁻¹ * L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_scale]; ring

theorem g₃_scale (L : PeriodPair) (α : ℂˣ) : (L.scale α).g₃ = ((α : ℂ) ^ 6)⁻¹ * L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_scale]; ring

theorem g₂_ofTau (τ : ℍ) : (ofTau τ).g₂ = (120 * riemannZeta 4) * E₄ τ := by
  rw [PeriodPair.g₂, G_ofTau_eq (by norm_num : 3 ≤ 4)]; push_cast; ring

theorem g₃_ofTau (τ : ℍ) : (ofTau τ).g₃ = (280 * riemannZeta 6) * E₆ τ := by
  rw [PeriodPair.g₃, G_ofTau_eq (by norm_num : 3 ≤ 6)]; push_cast; ring

theorem mem_scale_lattice (L : PeriodPair) (α : ℂˣ) (x : ℂ) :
    x ∈ (L.scale α).lattice ↔ ∃ m n : ℤ, (α : ℂ) * (m * L.ω₁ + n * L.ω₂) = x := by
  rw [mem_lattice]
  simp only [scale_ω₁, scale_ω₂]
  constructor
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩
  · rintro ⟨m, n, rfl⟩; exact ⟨m, n, by ring⟩

theorem C₄_ne_zero : (120 * riemannZeta 4 : ℂ) ≠ 0 :=
  mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_le_re (by norm_num))

theorem C₆_ne_zero : (280 * riemannZeta 6 : ℂ) ≠ 0 :=
  mul_ne_zero (by norm_num) (riemannZeta_ne_zero_of_one_le_re (by norm_num))

end Bridge

theorem E₄_cube_sub_E₆_sq_ne_zero (z : ℍ) : E₄ z ^ 3 - E₆ z ^ 2 ≠ 0 := fun h0 => by
  have h := ModularForm.discriminant_eq_E₄_cube_sub_E₆_sq z
  rw [h0, zero_div] at h
  exact ModularForm.discriminant_ne_zero z h

end ModularForm.Gamma0Separation
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.ModularForm P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.ModularForm.Gamma0Separation"
p2m_reactivate "P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne.ModularForm"

open ModularForm.Gamma0Separation in
theorem solution (N : ℕ) [NeZero N]
    (τ τ' : ℍ) (hτ : ∀ γ : CongruenceSubgroup.Gamma0 N, (γ : SL(2, ℤ)) • τ ≠ τ') :
    ∃ (k : ℤ) (g h : ModularForm (CongruenceSubgroup.Gamma0 N) k),
      (g : ℍ → ℂ) τ * (h : ℍ → ℂ) τ' ≠ (g : ℍ → ℂ) τ' * (h : ℍ → ℂ) τ := by
  by_contra H
  push Not at H

  set A := res N E₄ with hA
  set B := res N E₆ with hB
  set A' := liftN N E₄ with hA'
  set B' := liftN N E₆ with hB'
  have hN0 : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)

  have R1 := H 12 (((A.mul A).mul A).mcast (by norm_num)) ((B.mul B).mcast (by norm_num))
  have R2 := H 4 A A'
  have R3 := H 6 B B'
  have R4 := H 12 (((A.mul A).mul A).mcast (by norm_num)) ((B'.mul B').mcast (by norm_num))
  have R5 := H 12 ((B.mul B).mcast (by norm_num)) (((A'.mul A').mul A').mcast (by norm_num))
  simp only [hA, hB, hA', hB', coe_mcast, coe_mul, Pi.mul_apply, res_apply, liftN_apply]
    at R1 R2 R3 R4 R5

  have c4ne : (N : ℂ) ^ ((4 : ℤ) - 1) ≠ 0 := zpow_ne_zero _ hN0
  have c6ne : (N : ℂ) ^ ((6 : ℤ) - 1) ≠ 0 := zpow_ne_zero _ hN0
  generalize (N : ℂ) ^ ((4 : ℤ) - 1) = c₄ at R2 R5 c4ne
  generalize (N : ℂ) ^ ((6 : ℤ) - 1) = c₆ at R3 R4 c6ne

  obtain ⟨u, hu, hua, hub, hup, huq⟩ :=
    exists_scalar (a₁ := E₄ τ') (b₁ := E₆ τ') (p₁ := E₄ (mulN N τ')) (q₁ := E₆ (mulN N τ'))
      (a₂ := E₄ τ) (b₂ := E₆ τ) (p₂ := E₄ (mulN N τ)) (q₂ := E₆ (mulN N τ))
      (E₄_cube_sub_E₆_sq_ne_zero τ') (E₄_cube_sub_E₆_sq_ne_zero τ)
      (by linear_combination -R1)
      (mul_left_cancel₀ c4ne (by linear_combination -R2))
      (mul_left_cancel₀ c6ne (by linear_combination -R3))
      (mul_left_cancel₀ (pow_ne_zero 2 c6ne) (by linear_combination -R4))
      (mul_left_cancel₀ (pow_ne_zero 3 c4ne) (by linear_combination -R5))

  set uU : ℂˣ := Units.mk0 u hu with huU
  have hcoe : (uU : ℂ) = u := rfl
  have hΛ : (PeriodPair.ofTau τ').lattice = ((PeriodPair.ofTau τ).scale uU).lattice := by
    apply PeriodPair.lattice_eq_of_g2_eq_of_g3_eq
    · rw [g₂_scale, g₂_ofTau, g₂_ofTau, hua, hcoe]
      field_simp
    · rw [g₃_scale, g₃_ofTau, g₃_ofTau, hub, hcoe]
      field_simp
  have hΛN : (PeriodPair.ofTau (mulN N τ')).lattice =
      ((PeriodPair.ofTau (mulN N τ)).scale uU).lattice := by
    apply PeriodPair.lattice_eq_of_g2_eq_of_g3_eq
    · rw [g₂_scale, g₂_ofTau, g₂_ofTau, hup, hcoe]
      field_simp
    · rw [g₃_scale, g₃_ofTau, g₃_ofTau, huq, hcoe]
      field_simp

  obtain ⟨a, b, h1⟩ : ∃ a b : ℤ, u * (a * τ + b) = τ' := by
    have h := (PeriodPair.ofTau τ').ω₁_mem_lattice
    rw [hΛ, mem_scale_lattice] at h
    simpa only [PeriodPair.ofTau_ω₁, PeriodPair.ofTau_ω₂, mul_one, hcoe] using h
  obtain ⟨c, d, h2⟩ : ∃ c d : ℤ, u * (c * τ + d) = 1 := by
    have h := (PeriodPair.ofTau τ').ω₂_mem_lattice
    rw [hΛ, mem_scale_lattice] at h
    simpa only [PeriodPair.ofTau_ω₁, PeriodPair.ofTau_ω₂, mul_one, hcoe] using h
  obtain ⟨p, q, h3⟩ : ∃ p q : ℤ, p * (τ' : ℂ) + q = u * τ := by
    have h := ((PeriodPair.ofTau τ).scale uU).ω₁_mem_lattice
    rw [← hΛ, PeriodPair.mem_lattice] at h
    simpa only [PeriodPair.ofTau_ω₁, PeriodPair.ofTau_ω₂, PeriodPair.scale_ω₁, mul_one,
      hcoe] using h
  obtain ⟨r, s, h4⟩ : ∃ r s : ℤ, r * (τ' : ℂ) + s = u := by
    have h := ((PeriodPair.ofTau τ).scale uU).ω₂_mem_lattice
    rw [← hΛ, PeriodPair.mem_lattice] at h
    simpa only [PeriodPair.ofTau_ω₁, PeriodPair.ofTau_ω₂, PeriodPair.scale_ω₂, mul_one,
      hcoe] using h
  obtain ⟨e, f, h5⟩ : ∃ e f : ℤ, u * (e * (N * τ) + f) = 1 := by
    have h := (PeriodPair.ofTau (mulN N τ')).ω₂_mem_lattice
    rw [hΛN, mem_scale_lattice] at h
    simpa only [PeriodPair.ofTau_ω₁, PeriodPair.ofTau_ω₂, mul_one, hcoe, coe_mulN] using h
  obtain ⟨γ, hγ⟩ := exists_gamma0_of_lattice_rel N τ τ' hu h1 h2 h3 h4 h5
  exact hτ γ hγ

end
end S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne
end P2MW
export P2MW.S_ModularForm_exists_gamma0_apply_mul_apply_ne_of_forall_smul_ne (solution)
