-- Prove2me | solution 1 for ModularCurve.UVCrossingModel.exists_diagAut_fixed_iff
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/9e10b269-4dcf-5604-ba3a-17c6afb49b3c

import Mathlib
import Definitions.Def_ModularCurve_UVCrossingModel
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff

set_option autoImplicit false

open MvPowerSeries

namespace GaussPencil
namespace L9d

variable {W : Type*} [CommRing W]

noncomputable def ij (a b : ℕ) : Fin 2 →₀ ℕ := Finsupp.single 0 a + Finsupp.single 1 b

@[scoped simp] theorem ij_zero (a b : ℕ) : ij a b 0 = a := by simp [ij]
@[scoped simp] theorem ij_one (a b : ℕ) : ij a b 1 = b := by simp [ij]

theorem eq_ij (d : Fin 2 →₀ ℕ) : d = ij (d 0) (d 1) := by
  ext i; fin_cases i <;> simp

theorem ij_injective' {a b a' b' : ℕ} (h : ij a b = ij a' b') : a = a' ∧ b = b' := by
  have h0 := congrArg (fun d => d 0) h
  have h1 := congrArg (fun d => d 1) h
  simp only [ij_zero, ij_one] at h0 h1
  exact ⟨h0, h1⟩

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

section Unique

variable (π : W) (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0)

include hsep in

theorem eq_zero_of_reduced_of_eq_crossing_mul {D H : MvPowerSeries (Fin 2) W}
    (hred : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → coeff (ij a b) D = 0) (hD : D = crossing π * H) : D = 0 := by

  have hstep : ∀ a b : ℕ, coeff (ij a b) H = π * coeff (ij (a + 1) (b + 1)) H := by
    intro a b
    have h := hred (a + 1) (b + 1) (by omega) (by omega)
    rw [hD, coeff_crossing_mul, if_pos ⟨by omega, by omega⟩, Nat.add_sub_cancel, Nat.add_sub_cancel, sub_eq_zero] at h
    exact h
  have hdiv : ∀ k a b : ℕ, coeff (ij a b) H = π ^ k * coeff (ij (a + k) (b + k)) H := by
    intro k
    induction k with
    | zero => intro a b; simp
    | succ k ih =>
      intro a b
      rw [ih, hstep (a + k) (b + k), pow_succ, mul_assoc]
      rfl
  have hH : H = 0 := by
    refine MvPowerSeries.ext fun d => ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
    rw [map_zero]
    exact hsep _ fun k => ⟨_, hdiv k a b⟩
  rw [hD, hH, mul_zero]

end Unique

section Diag

variable (ζ ζ' : W) (hζζ' : ζ * ζ' = 1)

def cvec : Fin 2 → W := ![ζ, ζ']
def cvec' : Fin 2 → W := ![ζ', ζ]

include hζζ' in
theorem cvec_mul_cvec' : cvec ζ ζ' * cvec' ζ ζ' = 1 := by
  funext i; fin_cases i
  · show ζ * ζ' = 1; exact hζζ'
  · show ζ' * ζ = 1; rw [mul_comm]; exact hζζ'

include hζζ' in
theorem cvec'_mul_cvec : cvec' ζ ζ' * cvec ζ ζ' = 1 := by
  rw [mul_comm]; exact cvec_mul_cvec' ζ ζ' hζζ'

theorem prod_ij (c : Fin 2 → W) (a b : ℕ) : ((ij a b).prod fun s m => c s ^ m) = c 0 ^ a * c 1 ^ b := by
  rw [ij, Finsupp.prod_add_index', Finsupp.prod_single_index, Finsupp.prod_single_index]
  · exact pow_zero _
  · exact pow_zero _
  · intro i; exact pow_zero _
  · intro i m n; exact pow_add _ _ _

theorem coeff_rescale_ij (c : Fin 2 → W) (F : MvPowerSeries (Fin 2) W) (a b : ℕ) :
    coeff (ij a b) (rescale c F) = c 0 ^ a * c 1 ^ b * coeff (ij a b) F := by
  rw [coeff_rescale, prod_ij]

theorem rescale_C' (c : Fin 2 → W) (w : W) : rescale c (C w : MvPowerSeries (Fin 2) W) = C w := by
  refine MvPowerSeries.ext fun d => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
  rw [coeff_rescale_ij, coeff_C]
  split_ifs with h
  · have h0 := congrArg (fun d => d 0) h
    have h1 := congrArg (fun d => d 1) h
    simp only [ij_zero, ij_one, Finsupp.coe_zero, Pi.zero_apply] at h0 h1
    rw [h0, h1, pow_zero, pow_zero, one_mul, one_mul]
  · rw [mul_zero]

include hζζ' in

noncomputable def rescaleAlgEquiv : MvPowerSeries (Fin 2) W ≃ₐ[W] MvPowerSeries (Fin 2) W :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.ofRingHom (rescale (cvec ζ ζ')) (rescale (cvec' ζ ζ'))
      (by rw [← rescale_mul, cvec'_mul_cvec ζ ζ' hζζ', rescale_one])
      (by rw [← rescale_mul, cvec_mul_cvec' ζ ζ' hζζ', rescale_one]))
    (fun w => rescale_C' _ w)

theorem rescaleAlgEquiv_apply (F : MvPowerSeries (Fin 2) W) :
    rescaleAlgEquiv ζ ζ' hζζ' F = rescale (cvec ζ ζ') F := rfl

include hζζ' in
theorem rescale_crossing (π : W) : rescale (cvec ζ ζ') (crossing π) = crossing π := by
  rw [crossing, X_mul_X_eq, map_sub, rescale_C']
  congr 1
  refine MvPowerSeries.ext fun d => ?_
  obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
  rw [coeff_rescale_ij, coeff_monomial]
  split_ifs with h
  · obtain ⟨ha, hb⟩ := ij_injective' h
    subst ha; subst hb
    show ζ ^ 1 * ζ' ^ 1 * 1 = 1
    rw [pow_one, pow_one, mul_one, hζζ']
  · rw [mul_zero]

end Diag

end GaussPencil.L9d
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff.GaussPencil P2MW.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff.GaussPencil.L9d"
p2m_reactivate "P2MW.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff.GaussPencil"

open ModularCurve ModularCurve.UVCrossingModel GaussPencil.L9d

theorem solution
    {W : Type*} [CommRing W] (π : W) [IsPrecomplete (Ideal.span {π}) W]
    (hsep : ∀ x : W, (∀ n : ℕ, π ^ n ∣ x) → x = 0) (e : ℕ) (he : e ≠ 0)
    (ζ ζ' : W) (hζ : ζ ^ e = 1) (hζζ' : ζ * ζ' = 1)
    (hreg : ∀ m : ℕ, 0 < m → m < e → ζ ^ m - 1 ∈ nonZeroDivisors W) :
    ∃ δ : UVCrossingModel W π ≃ₐ[W] UVCrossingModel W π,
      (∀ F : MvPowerSeries (Fin 2) W, δ (mk π F) = mk π (MvPowerSeries.rescale ![ζ, ζ'] F)) ∧
      ∀ z : UVCrossingModel W π, δ z = z ↔
        ∃ F : MvPowerSeries (Fin 2) W,
          (∀ d : Fin 2 →₀ ℕ, MvPowerSeries.coeff d F ≠ 0 → (e : ℤ) ∣ (d 0 : ℤ) - d 1) ∧ mk π F = z := by
  classical

  have hζ' : ζ' ^ e = 1 := by
    have : (ζ * ζ') ^ e = 1 := by rw [hζζ', one_pow]
    rwa [mul_pow, hζ, one_mul] at this
  have hpow : ∀ a b : ℕ, (e : ℤ) ∣ (a : ℤ) - b → ζ ^ a * ζ' ^ b = 1 := by
    intro a b hab
    rcases le_total b a with h | h
    · obtain ⟨k, hk⟩ : e ∣ a - b := by
        have : ((a - b : ℕ) : ℤ) = (a : ℤ) - b := by push_cast [h]; ring
        exact Int.natCast_dvd_natCast.mp (this ▸ hab)
      have : ζ ^ a * ζ' ^ b = ζ ^ (a - b) * (ζ * ζ') ^ b := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel h]
      rw [this, hζζ', one_pow, mul_one, hk, pow_mul, hζ, one_pow]
    · obtain ⟨k, hk⟩ : e ∣ b - a := by
        have : ((b - a : ℕ) : ℤ) = -((a : ℤ) - b) := by push_cast [h]; ring
        exact Int.natCast_dvd_natCast.mp (this ▸ (dvd_neg.mpr hab))
      have : ζ ^ a * ζ' ^ b = (ζ * ζ') ^ a * ζ' ^ (b - a) := by
        rw [mul_pow, mul_assoc, ← pow_add, Nat.add_sub_cancel' h]
      rw [this, hζζ', one_pow, one_mul, hk, pow_mul, hζ', one_pow]

  have hregζ : ∀ a : ℕ, ¬ e ∣ a → ∀ x : W, (ζ ^ a - 1) * x = 0 → x = 0 := by
    intro a ha x hx
    have hr : ζ ^ a = ζ ^ (a % e) := by
      conv_lhs => rw [← Nat.div_add_mod a e, pow_add, pow_mul, hζ, one_pow, one_mul]
    have hm0 : 0 < a % e := Nat.pos_of_ne_zero fun h0 => ha (Nat.dvd_of_mod_eq_zero h0)
    have hme : a % e < e := Nat.mod_lt a (Nat.pos_of_ne_zero he)
    rw [hr] at hx
    exact (mem_nonZeroDivisors_iff.mp (hreg _ hm0 hme)).1 x hx
  have hregζ' : ∀ b : ℕ, ¬ e ∣ b → ∀ x : W, (ζ' ^ b - 1) * x = 0 → x = 0 := by
    intro b hb x hx

    have hz : ζ' = ζ ^ (e - 1) := by
      have h1 : ζ * ζ ^ (e - 1) = 1 := by rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr he), hζ]
      calc ζ' = ζ' * (ζ * ζ ^ (e - 1)) := by rw [h1, mul_one]
        _ = (ζ * ζ') * ζ ^ (e - 1) := by ring
        _ = ζ ^ (e - 1) := by rw [hζζ', one_mul]
    rw [hz, ← pow_mul] at hx
    refine hregζ ((e - 1) * b) ?_ x hx
    intro hd
    apply hb
    have hcop : Nat.Coprime e (e - 1) := by
      have := Nat.coprime_self_sub_right (Nat.one_le_iff_ne_zero.mpr he) (n := e) (m := 1)
      simpa using this
    exact hcop.dvd_of_dvd_mul_left hd

  have hI : uvCrossingIdeal W π = (uvCrossingIdeal W π).map
      (rescaleAlgEquiv ζ ζ' hζζ' : MvPowerSeries (Fin 2) W →+* MvPowerSeries (Fin 2) W) := by
    show Ideal.span _ = Ideal.map _ (Ideal.span _)
    rw [Ideal.map_span, Set.image_singleton]
    congr 2
    exact (rescale_crossing ζ ζ' hζζ' π).symm
  let δ : UVCrossingModel W π ≃ₐ[W] UVCrossingModel W π :=
    Ideal.quotientEquivAlg (uvCrossingIdeal W π) (uvCrossingIdeal W π) (rescaleAlgEquiv ζ ζ' hζζ') hI
  have hδ : ∀ F : MvPowerSeries (Fin 2) W, δ (mk π F) = mk π (MvPowerSeries.rescale (cvec ζ ζ') F) := fun F => rfl
  refine ⟨δ, fun F => hδ F, fun z => ⟨fun hz => ?_, ?_⟩⟩
  ·
    obtain ⟨F₀, rfl⟩ := mk_surjective π z
    set N := nf π F₀ with hN
    have hFN : mk π F₀ = mk π N := by
      show Ideal.Quotient.mk (uvCrossingIdeal W π) F₀ = Ideal.Quotient.mk (uvCrossingIdeal W π) N
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
      exact ⟨tail π F₀, by rw [mul_comm]; exact (sub_nf_eq π hsep F₀).symm⟩
    have hredN : ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → MvPowerSeries.coeff (ij a b) N = 0 := by
      intro a b ha hb; rw [coeff_nf, if_neg (by omega), if_neg (by omega)]

    have hfix : MvPowerSeries.rescale (cvec ζ ζ') N = N := by
      have h1 : mk π (MvPowerSeries.rescale (cvec ζ ζ') N) = mk π N := by rw [← hδ, ← hFN]; exact hz
      have h2 : MvPowerSeries.rescale (cvec ζ ζ') N - N ∈ uvCrossingIdeal W π := by
        have : Ideal.Quotient.mk (uvCrossingIdeal W π) (MvPowerSeries.rescale (cvec ζ ζ') N)
            = Ideal.Quotient.mk (uvCrossingIdeal W π) N := h1
        exact Ideal.Quotient.eq.mp this
      obtain ⟨H, hH⟩ := Ideal.mem_span_singleton'.mp h2
      have h3 := eq_zero_of_reduced_of_eq_crossing_mul π hsep (D := MvPowerSeries.rescale (cvec ζ ζ') N - N) (H := H)
        (fun a b ha hb => by rw [map_sub, coeff_rescale_ij, hredN a b ha hb, mul_zero, sub_zero])
        (by rw [← hH, mul_comm]; rfl)
      exact sub_eq_zero.mp h3
    refine ⟨N, fun d hd => ?_, hFN.symm⟩
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
    simp only [ij_zero, ij_one]
    have hc := congrArg (MvPowerSeries.coeff (ij a b)) hfix
    rw [coeff_rescale_ij] at hc

    have hc' : (ζ ^ a * ζ' ^ b - 1) * MvPowerSeries.coeff (ij a b) N = 0 := by rw [sub_mul, one_mul, sub_eq_zero]; exact hc
    by_cases hb0 : b = 0
    · subst hb0
      by_cases hea : e ∣ a
      · push_cast; rw [sub_zero]; exact Int.natCast_dvd_natCast.mpr hea
      · exfalso; apply hd
        simp only [pow_zero, mul_one] at hc'
        exact hregζ a hea _ hc'
    by_cases ha0 : a = 0
    · subst ha0
      by_cases heb : e ∣ b
      · push_cast; rw [zero_sub, dvd_neg]; exact Int.natCast_dvd_natCast.mpr heb
      · exfalso; apply hd
        simp only [pow_zero, one_mul] at hc'
        exact hregζ' b heb _ hc'
    · exact absurd (hredN a b (by omega) (by omega)) hd
  ·
    rintro ⟨F, hF, rfl⟩
    rw [hδ]
    congr 1
    refine MvPowerSeries.ext fun d => ?_
    obtain ⟨a, b, rfl⟩ : ∃ a b : ℕ, d = ij a b := ⟨d 0, d 1, eq_ij d⟩
    rw [coeff_rescale_ij]
    by_cases h0 : MvPowerSeries.coeff (ij a b) F = 0
    · rw [h0, mul_zero]
    · have := hF _ h0
      simp only [ij_zero, ij_one] at this
      rw [show cvec ζ ζ' 0 = ζ from rfl, show cvec ζ ζ' 1 = ζ' from rfl, hpow a b this, one_mul]

end S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff
end P2MW
export P2MW.S_ModularCurve_UVCrossingModel_exists_diagAut_fixed_iff (solution)
