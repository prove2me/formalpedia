-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_mk_eq_mk_expand_of_dvd_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/ff58e342-cb57-5a0c-a84a-5c1d324272fa

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub

set_option autoImplicit false

open MvPowerSeries

namespace GaussPencil
namespace L9b

variable {W : Type*} [CommRing W]

noncomputable def ij (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[scoped simp] theorem ij_zero (a b : ℕ) : ij a b 0 = a := by simp [ij]
@[scoped simp] theorem ij_one (a b : ℕ) : ij a b 1 = b := by simp [ij]

theorem eq_ij (d : Fin 2 →₀ ℕ) : d = ij (d 0) (d 1) := by
  ext i; fin_cases i <;> simp

theorem smul_ij (e a b : ℕ) : e • ij a b = ij (e * a) (e * b) := by
  ext i; fin_cases i <;> simp [ij]

theorem ij_le_ij_iff {a b a' b' : ℕ} : ij a b ≤ ij a' b' ↔ a ≤ a' ∧ b ≤ b' := by
  constructor
  · intro h; exact ⟨by simpa using h 0, by simpa using h 1⟩
  · rintro ⟨ha, hb⟩ i; fin_cases i <;> simpa

theorem ij_sub_ij (a b a' b' : ℕ) : ij a b - ij a' b' = ij (a - a') (b - b') := by
  ext i; fin_cases i <;> simp [ij]

noncomputable def crossing (c : W) : MvPowerSeries (Fin 2) W := X 0 * X 1 - C c

theorem X_mul_X_eq : (X 0 * X 1 : MvPowerSeries (Fin 2) W) = monomial (ij 1 1) 1 := by
  rw [X_def, X_def, monomial_mul_monomial, one_mul]; rfl

theorem coeff_crossing_mul (c : W) (G : MvPowerSeries (Fin 2) W) (a b : ℕ) :
    coeff (ij a b) (crossing c * G)
      = (if 1 ≤ a ∧ 1 ≤ b then coeff (ij (a - 1) (b - 1)) G else 0) - c * coeff (ij a b) G := by
  rw [crossing, sub_mul, map_sub, X_mul_X_eq, coeff_monomial_mul, coeff_C_mul, one_mul]
  by_cases hab : 1 ≤ a ∧ 1 ≤ b
  · rw [if_pos (ij_le_ij_iff.mpr hab), if_pos hab, ij_sub_ij]
  · rw [if_neg (fun h => hab (ij_le_ij_iff.mp h)), if_neg hab]

section Sums

variable (π : W) [IsPrecomplete (Ideal.span {π}) W] (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0)

noncomputable def ps (w : ℕ → W) (k : ℕ) : W := (Finset.range k).sum fun m => w m * π ^ m

omit [IsPrecomplete (Ideal.span {π}) W] in
theorem ps_succ (w : ℕ → W) (k : ℕ) : ps π w (k + 1) = ps π w k + w k * π ^ k := by
  rw [ps, ps, Finset.sum_range_succ]

omit [IsPrecomplete (Ideal.span {π}) W] in
theorem ps_succ' (w : ℕ → W) (k : ℕ) : ps π w (k + 1) = w 0 + π * ps π (fun m => w (m + 1)) k := by
  rw [ps, ps, Finset.sum_range_succ', Finset.mul_sum, pow_zero, mul_one, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [pow_succ]; ring

omit [IsPrecomplete (Ideal.span {π}) W] in
theorem mem_smul_top_iff (k : ℕ) (x : W) :
    x ∈ (Ideal.span {π} ^ k • ⊤ : Submodule W W) ↔ π ^ k ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

omit [IsPrecomplete (Ideal.span {π}) W] in
theorem ps_dvd_sub (w : ℕ → W) {m n : ℕ} (h : m ≤ n) : π ^ m ∣ ps π w n - ps π w m := by
  induction n, h using Nat.le_induction with
  | base => simp
  | succ n hmn ih =>
    rw [ps_succ, add_sub_right_comm]
    exact dvd_add ih (dvd_mul_of_dvd_right (pow_dvd_pow π hmn) (w n))

theorem exists_lim (w : ℕ → W) : ∃ L : W, ∀ k : ℕ, π ^ k ∣ L - ps π w k := by
  have h : ∀ {m n : ℕ}, m ≤ n → ps π w m ≡ ps π w n [SMOD (Ideal.span {π} ^ m • ⊤ : Submodule W W)] := by
    intro m n hmn
    rw [SModEq.sub_mem, mem_smul_top_iff, ← dvd_neg, neg_sub]
    exact ps_dvd_sub π w hmn
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (inferInstance : IsPrecomplete (Ideal.span {π}) W) h
  refine ⟨L, fun k => ?_⟩
  have := hL k
  rw [SModEq.sub_mem, mem_smul_top_iff] at this
  rw [← dvd_neg, neg_sub]; exact this

noncomputable def S (w : ℕ → W) : W := Classical.choose (exists_lim π w)

theorem S_spec (w : ℕ → W) (k : ℕ) : π ^ k ∣ S π w - ps π w k := Classical.choose_spec (exists_lim π w) k

include hsep in

theorem eq_of_forall_dvd_sub {x y : W} (w : ℕ → W) (hx : ∀ k, π ^ k ∣ x - ps π w k) (hy : ∀ k, π ^ k ∣ y - ps π w k) :
    x = y := by
  have : x - y = 0 := hsep _ fun k => by
    have := dvd_sub (hx k) (hy k); rwa [sub_sub_sub_cancel_right] at this
  exact sub_eq_zero.mp this

include hsep in

theorem S_eq_add_mul_S (w : ℕ → W) : S π w = w 0 + π * S π (fun m => w (m + 1)) := by
  apply eq_of_forall_dvd_sub π hsep w (S_spec π w)
  intro k
  cases k with
  | zero => simp
  | succ k =>
    rw [ps_succ', add_sub_add_left_eq_sub, ← mul_sub, pow_succ']
    exact mul_dvd_mul_left π (S_spec π _ k)

include hsep in
theorem S_zero' (w : ℕ → W) (hw : ∀ m, w m = 0) : S π w = 0 := by
  apply eq_of_forall_dvd_sub π hsep w (S_spec π w)
  intro k
  rw [zero_sub, dvd_neg, ps]
  exact Finset.dvd_sum fun m _ => by rw [hw m, zero_mul]; exact dvd_zero _

end Sums

section NormalForm

variable (π : W) [IsPrecomplete (Ideal.span {π}) W] (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0)
variable (F : MvPowerSeries (Fin 2) W)

noncomputable def rayX (a₀ : ℕ) : ℕ → W := fun n => coeff (ij (a₀ + n) n) F

noncomputable def rayY (b₀ : ℕ) : ℕ → W := fun n => coeff (ij n (b₀ + n)) F

noncomputable def nf : MvPowerSeries (Fin 2) W := fun d =>
  if d 1 = 0 then S π (rayX F (d 0)) else if d 0 = 0 then S π (rayY F (d 1)) else 0

noncomputable def tail : MvPowerSeries (Fin 2) W := fun d =>
  if d 1 ≤ d 0 then S π (fun m => rayX F (d 0 - d 1) (d 1 + 1 + m))
  else S π (fun m => rayY F (d 1 - d 0) (d 0 + 1 + m))

theorem coeff_nf (a b : ℕ) : coeff (ij a b) (nf π F)
    = if b = 0 then S π (rayX F a) else if a = 0 then S π (rayY F b) else 0 := by
  rw [coeff_apply]; simp [nf]

theorem coeff_tail (a b : ℕ) : coeff (ij a b) (tail π F)
    = if b ≤ a then S π (fun m => rayX F (a - b) (b + 1 + m)) else S π (fun m => rayY F (b - a) (a + 1 + m)) := by
  rw [coeff_apply]; simp [tail]

include hsep in

theorem sub_nf_eq : F - nf π F = crossing π * tail π F := by
  refine MvPowerSeries.ext fun d => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
  rw [map_sub, coeff_crossing_mul, coeff_nf]
  simp only [coeff_tail]
  by_cases hb0 : b = 0
  ·
    subst hb0
    rw [if_neg (show ¬ (1 ≤ a ∧ 1 ≤ 0) by omega), if_pos rfl, if_pos (Nat.zero_le a), zero_sub, Nat.sub_zero,
      S_eq_add_mul_S π hsep (rayX F a)]
    have h1 : rayX F a 0 = coeff (ij a 0) F := by simp only [rayX, add_zero]
    have h2 : (fun m => rayX F a (0 + 1 + m)) = fun m => rayX F a (m + 1) := by
      funext m; congr 1; omega
    rw [h1, h2]; ring
  by_cases ha0 : a = 0
  ·
    subst ha0
    rw [if_neg (show ¬ (1 ≤ 0 ∧ 1 ≤ b) by omega), if_neg hb0, if_pos rfl, if_neg (show ¬ b ≤ 0 by omega),
      zero_sub, Nat.sub_zero, S_eq_add_mul_S π hsep (rayY F b)]
    have h1 : rayY F b 0 = coeff (ij 0 b) F := by simp only [rayY, add_zero]
    have h2 : (fun m => rayY F b (0 + 1 + m)) = fun m => rayY F b (m + 1) := by
      funext m; congr 1; omega
    rw [h1, h2]; ring

  rw [if_neg hb0, if_neg ha0, sub_zero, if_pos (show 1 ≤ a ∧ 1 ≤ b by omega)]
  by_cases hba : b ≤ a
  · rw [if_pos (show b - 1 ≤ a - 1 by omega), if_pos hba, show a - 1 - (b - 1) = a - b by omega,
      S_eq_add_mul_S π hsep (fun m => rayX F (a - b) (b - 1 + 1 + m))]
    have h1 : rayX F (a - b) (b - 1 + 1 + 0) = coeff (ij a b) F := by
      show coeff (ij (a - b + (b - 1 + 1 + 0)) (b - 1 + 1 + 0)) F = coeff (ij a b) F
      rw [show a - b + (b - 1 + 1 + 0) = a by omega, show b - 1 + 1 + 0 = b by omega]
    have h2 : (fun m => rayX F (a - b) (b - 1 + 1 + (m + 1))) = fun m => rayX F (a - b) (b + 1 + m) := by
      funext m; congr 1; omega
    rw [h1, h2]; ring
  · rw [if_neg (show ¬ b - 1 ≤ a - 1 by omega), if_neg hba, show b - 1 - (a - 1) = b - a by omega,
      S_eq_add_mul_S π hsep (fun m => rayY F (b - a) (a - 1 + 1 + m))]
    have h1 : rayY F (b - a) (a - 1 + 1 + 0) = coeff (ij a b) F := by
      show coeff (ij (a - 1 + 1 + 0) (b - a + (a - 1 + 1 + 0))) F = coeff (ij a b) F
      rw [show b - a + (a - 1 + 1 + 0) = b by omega, show a - 1 + 1 + 0 = a by omega]
    have h2 : (fun m => rayY F (b - a) (a - 1 + 1 + (m + 1))) = fun m => rayY F (b - a) (a + 1 + m) := by
      funext m; congr 1; omega
    rw [h1, h2]; ring

end NormalForm

end GaussPencil.L9b
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub.GaussPencil P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub.GaussPencil.L9b"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub.GaussPencil"

open ModularCurve ModularCurve.UVCrossingModel GaussPencil.L9b

theorem solution
    {W : Type*} [CommRing W] (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (e : ℕ) (he : e ≠ 0)
    (F : MvPowerSeries (Fin 2) W)
    (hF : ∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F ≠ 0 → (e : ℤ) ∣ (d 0 : ℤ) - d 1) :
    ∃ G : MvPowerSeries (Fin 2) W, mk π F = mk π (MvPowerSeries.expand e he G) := by
  classical

  have hX : ∀ a : ℕ, ¬ e ∣ a → S π (rayX F a) = 0 := by
    intro a ha
    apply S_zero' π hsep
    intro m
    by_contra h
    have := hF _ h
    simp only [ij_zero, ij_one] at this
    push_cast at this
    rw [add_sub_cancel_right] at this
    exact ha (Int.natCast_dvd_natCast.mp this)
  have hY : ∀ b : ℕ, ¬ e ∣ b → S π (rayY F b) = 0 := by
    intro b hb
    apply S_zero' π hsep
    intro m
    by_contra h
    have := hF _ h
    simp only [ij_zero, ij_one] at this
    push_cast at this
    have h' : (e : ℤ) ∣ -(b : ℤ) := by convert this using 1; ring
    rw [dvd_neg] at h'
    exact hb (Int.natCast_dvd_natCast.mp h')

  let G : MvPowerSeries (Fin 2) W := fun d =>
    if d 1 = 0 then S π (rayX F (e * d 0)) else if d 0 = 0 then S π (rayY F (e * d 1)) else 0
  have hG : ∀ a b : ℕ, MvPowerSeries.coeff (ij a b) G
      = if b = 0 then S π (rayX F (e * a)) else if a = 0 then S π (rayY F (e * b)) else 0 := by
    intro a b; rw [MvPowerSeries.coeff_apply]; simp [G]
  have hexp : MvPowerSeries.expand e he G = nf π F := by
    refine MvPowerSeries.ext fun d => ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
    rw [coeff_nf]
    by_cases hda : e ∣ a
    · by_cases hdb : e ∣ b
      · obtain ⟨a', rfl⟩ := hda
        obtain ⟨b', rfl⟩ := hdb
        rw [← smul_ij, MvPowerSeries.coeff_expand_smul, hG]
        simp only [Nat.mul_eq_zero, he, false_or]
      · rw [MvPowerSeries.coeff_expand_of_not_dvd e he G (i := 1) (by simpa using hdb)]
        have hb0 : b ≠ 0 := by rintro rfl; exact hdb (dvd_zero e)
        rw [if_neg hb0]
        by_cases ha0 : a = 0
        · rw [if_pos ha0, hY b hdb]
        · rw [if_neg ha0]
    · rw [MvPowerSeries.coeff_expand_of_not_dvd e he G (i := 0) (by simpa using hda)]
      have ha0 : a ≠ 0 := by rintro rfl; exact hda (dvd_zero e)
      by_cases hb0 : b = 0
      · rw [if_pos hb0, hX a hda]
      · rw [if_neg hb0, if_neg ha0]
  refine ⟨G, ?_⟩
  rw [hexp]
  show Ideal.Quotient.mk (uvCrossingIdeal W π) F = Ideal.Quotient.mk (uvCrossingIdeal W π) (nf π F)
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  exact ⟨tail π F, by rw [mul_comm]; exact (sub_nf_eq π hsep F).symm⟩

end S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_mk_eq_mk_expand_of_dvd_sub (solution)
