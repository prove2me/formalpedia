-- Prove2me | solution 1 for OAI.PlanarUnitDistances.AlgebraicObstruction.no_rectangles
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T02:57:36.724988+00:00
-- url     : https://prove2.me/submissions/fba7fc24-542b-4942-b9de-017968c6a8ba

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000
import Theorems.Thm_OAI_PlanarUnitDistances_AlgebraicObstruction_curve_curve
import Theorems.Thm_OAI_PlanarUnitDistances_AlgebraicObstruction_curve_plane

section
-- module Solutions.OAIQ2_Uni.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. The `dite` forms are stated as
`dite p a b`, not with the `if hp : p then …` notation: its eta-expanded lambdas form is a higher-order pattern
that `rw` cannot find (DepthThree, PeriodicTiling 2026-10-25). -/
section OAICompat434
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    dite p a b = a h := dif_pos h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Powers
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PowerGrowth
open Filter

variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Lower.mono (hf : Lower F t f a) (h : f ≤ᶠ[F] g) : Lower F t g a := by
  intro ε hε
  filter_upwards [hf ε hε,h] with i hi hfg
  exact hi.trans hfg

lemma Upper.mono (hg : Upper F t g a) (h : f ≤ᶠ[F] g) : Upper F t f a := by
  intro ε hε
  filter_upwards [hg ε hε,h] with i hi hfg
  exact hfg.trans hi

lemma Lower.congr (hf : Lower F t f a) (h : f =ᶠ[F] g) : Lower F t g a :=
  hf.mono h.le

lemma Upper.congr (hf : Upper F t f a) (h : f =ᶠ[F] g) : Upper F t g a :=
  hf.mono h.symm.le

lemma eventually_one_le (ht : Tendsto t F atTop) : ∀ᶠ i in F,1 ≤ t i :=
  ht.eventually_ge_atTop 1

lemma eventually_base_pos (ht : Tendsto t F atTop) : ∀ᶠ i in F,0 < t i :=
  (eventually_one_le ht).mono fun _ hi => lt_of_lt_of_le zero_lt_one hi

lemma Upper.exponent_mono (hf : Upper F t f a) (h : a ≤ b)
    (ht : Tendsto t F atTop) : Upper F t f b := by
  intro ε hε
  filter_upwards [hf ε hε,eventually_one_le ht] with i hi hti
  exact hi.trans (Real.rpow_le_rpow_of_exponent_le hti (by linarith))

lemma Lower.eventually_pos (hf : Lower F t f a) (ht : Tendsto t F atTop) :
    ∀ᶠ i in F,0 < f i := by
  filter_upwards [hf 1 zero_lt_one,eventually_base_pos ht] with i hi hti
  exact (Real.rpow_pos_of_pos hti _).trans_le hi

lemma Lower.mul (hf : Lower F t f a) (hg : Lower F t g b)
    (ht : Tendsto t F atTop) : Lower F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),eventually_base_pos ht]
    with i hi hj hti
  have he : a+b-ε=(a-ε/2)+(b-ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj (Real.rpow_nonneg hti.le _) ((Real.rpow_nonneg hti.le _).trans hi)

lemma Upper.mul (hf : Upper F t f a) (hg : Upper F t g b)
    (hnf : ∀ᶠ i in F,0 ≤ f i) (hng : ∀ᶠ i in F,0 ≤ g i)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i*g i) (a+b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hnf,hng,eventually_base_pos ht]
    with i hi hj _ hj0 hti
  have he : a+b+ε=(a+ε/2)+(b+ε/2) := by ring
  rw [he,Real.rpow_add hti]
  exact mul_le_mul hi hj hj0 (Real.rpow_nonneg hti.le _)

lemma eventually_constant_le_rpow (ht : Tendsto t F atTop) {ε : ℝ} (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ i in F,C ≤ t i ^ ε := by
  exact (_root_.tendsto_rpow_atTop hε |>.comp ht).eventually_ge_atTop C

lemma Lower.const_mul (hf : Lower F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 < C) : Lower F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C⁻¹,eventually_base_pos ht] with i hi hc hti
  have hc' : 1 ≤ C*(t i)^(ε/2) := by simpa only [mul_comm] using (inv_le_iff_one_le_mul₀ hC).mp hc
  have he : a-ε/2=(a-ε)+ε/2 := by ring
  have hpos := Real.rpow_nonneg hti.le (a-ε)
  calc
    (t i)^(a-ε) ≤ (t i)^(a-ε)*(C*(t i)^(ε/2)) := le_mul_of_one_le_right hpos hc'
    _ = C*(t i)^(a-ε/2) := by
      conv_rhs => rw [he,Real.rpow_add hti]
      ring
    _ ≤ C*f i := mul_le_mul_of_nonneg_left hi hC.le

lemma Upper.const_mul (hf : Upper F t f a) (ht : Tendsto t F atTop)
    {C : ℝ} (hC : 0 ≤ C) : Upper F t (fun i => C*f i) a := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),eventually_constant_le_rpow ht
    (show 0<ε/2 by positivity) C,eventually_base_pos ht] with i hi hc hti
  have he : a+ε=ε/2+(a+ε/2) := by ring
  calc
    C*f i ≤ C*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_left hi hC
    _ ≤ (t i)^(ε/2)*(t i)^(a+ε/2) := mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hti.le _)
    _ = (t i)^(a+ε) := by rw [he]; exact (Real.rpow_add hti _ _).symm

lemma Upper.add (hf : Upper F t f a) (hg : Upper F t g a)
    (ht : Tendsto t F atTop) : Upper F t (fun i => f i+g i) a := by
  have hmax : Upper F t (fun i => max (f i) (g i)) a := by
    intro ε hε
    filter_upwards [hf ε hε,hg ε hε] with i hi hj
    exact max_le hi hj
  exact (hmax.const_mul ht (show (0:ℝ)≤2 by norm_num)).mono
    (Eventually.of_forall fun i => by dsimp; linarith [le_max_left (f i) (g i),le_max_right (f i) (g i)])

lemma Lower.div (hf : Lower F t f a) (hg : Upper F t g b)
    (hng : ∀ᶠ i in F,0 < g i) (ht : Tendsto t F atTop) :
    Lower F t (fun i => f i/g i) (a-b) := by
  intro ε hε
  filter_upwards [hf (ε/2) (by positivity),hg (ε/2) (by positivity),hng,eventually_base_pos ht]
    with i hi hj hj0 hti
  have he : a-b-ε=(a-ε/2)-(b+ε/2) := by ring
  rw [he,Real.rpow_sub hti]
  exact div_le_div₀ ((Real.rpow_nonneg hti.le _).trans hi) hi hj0 hj

end PlanarUnitDistances.PowerGrowth

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_AbsoluteValues
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset
noncomputable section

section Entries
variable (K : Type*) [Field K] [NumberField K]

lemma infiniteEntry_count : Fintype.card (K →ₐ[ℚ] ℂ) = Module.finrank ℚ K :=
  AlgHom.card ℚ K ℂ

end Entries

end
end PlanarUnitDistances.WeightedAbsoluteValues

namespace PlanarUnitDistances.ExactHeightLocal

open scoped BigOperators

section Local
variable {K : Type*} [Field K]

theorem abv_root_le (v : AbsoluteValue K ℝ) {m : ℕ} (hm : 0 < m)
    (a : Fin m → K) (u : K) (hu : u ^ m = ∑ i, a i * u ^ (i : ℕ)) :
    max (v u) 1 ≤ (m : ℝ) * ∏ i, max (v (a i)) 1 := by
  let A := ∏ i, max (v (a i)) 1
  have hA : 1 ≤ A := Finset.one_le_prod fun i _ => le_max_right _ _
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hbase : 1 ≤ (m : ℝ) * A := by nlinarith
  apply max_le _ hbase
  by_cases hv : v u ≤ 1
  · exact hv.trans hbase
  have hv1 : 1 < v u := lt_of_not_ge hv
  have hcoeff (i : Fin m) : v (a i) ≤ A := by
    exact Finset.le_prod_max_one (Finset.mem_univ i) (fun j => v (a j))
  have hp (i : Fin m) : (v u) ^ (i : ℕ) ≤ (v u) ^ (m - 1) :=
    pow_le_pow_right₀ hv1.le (by omega)
  have hsum : (v u) ^ m ≤ (m : ℝ) * (A * (v u) ^ (m - 1)) := by
    calc
      (v u) ^ m = v (∑ i, a i * u ^ (i : ℕ)) := by rw [← hu, map_pow]
      _ ≤ ∑ i, v (a i * u ^ (i : ℕ)) := v.sum_le _ _
      _ ≤ ∑ _i : Fin m, A * (v u) ^ (m - 1) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [map_mul, map_pow]
        exact mul_le_mul (hcoeff i) (hp i) (pow_nonneg (v.nonneg u) _) (by positivity)
      _ = (m : ℝ) * (A * (v u) ^ (m - 1)) := by simp
  have hpow : 0 < (v u) ^ (m - 1) := pow_pos (lt_trans zero_lt_one hv1) _
  have hrewrite : (v u) ^ m = (v u) * (v u) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hrewrite, ← mul_assoc] at hsum
  exact (mul_le_mul_iff_left₀ hpow).mp hsum

theorem nonarch_root_le (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {m : ℕ} (hm : 0 < m) (a : Fin m → K) (u : K)
    (hu : u ^ m = ∑ i, a i * u ^ (i : ℕ)) :
    max (v u) 1 ≤ ∏ i, max (v (a i)) 1 := by
  let A := ∏ i, max (v (a i)) 1
  have hA : 1 ≤ A := Finset.one_le_prod fun i _ => le_max_right _ _
  apply max_le _ hA
  by_cases hu1 : v u ≤ 1
  · exact hu1.trans hA
  have hv1 : 1 < v u := lt_of_not_ge hu1
  have hcoeff (i : Fin m) : v (a i) ≤ A :=
    Finset.le_prod_max_one (Finset.mem_univ i) (fun j => v (a j))
  have hp (i : Fin m) : (v u) ^ (i : ℕ) ≤ (v u) ^ (m - 1) :=
    pow_le_pow_right₀ hv1.le (by omega)
  have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hsum : (v u) ^ m ≤ A * (v u) ^ (m - 1) := by
    calc
      (v u) ^ m = v (∑ i, a i * u ^ (i : ℕ)) := by rw [← hu, map_pow]
      _ ≤ ⨆ i, v (a i * u ^ (i : ℕ)) := hv.apply_sum_univ_le
      _ ≤ A * (v u) ^ (m - 1) := by
        apply ciSup_le
        intro i
        rw [map_mul, map_pow]
        exact mul_le_mul (hcoeff i) (hp i) (pow_nonneg (v.nonneg u) _) (by positivity)
  have hpow : 0 < (v u) ^ (m - 1) := pow_pos (lt_trans zero_lt_one hv1) _
  have hrewrite : (v u) ^ m = (v u) * (v u) ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hrewrite] at hsum
  exact (mul_le_mul_iff_left₀ hpow).mp hsum

end Local

end PlanarUnitDistances.ExactHeightLocal

namespace PlanarUnitDistances.WeightedAbsoluteValues
open scoped BigOperators
open Finset Real ExactHeightLocal
noncomputable section
variable (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]

lemma posLog_max_one (r : ℝ) (hr : 0 ≤ r) : log⁺ (max r 1) = log⁺ r := by
  rw [posLog_eq_log_max_one (by positivity),posLog_eq_log_max_one hr]
  congr 1
  simp [max_comm]

omit [NumberField K] [IsGalois ℚ K] in
lemma local_posLog_root (v : AbsoluteValue K ℝ) {m : ℕ} (hm : 0 < m)
    (a : Fin m → K) (x : K) (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    log⁺ (v x) ≤ log m + ∑ i, log⁺ (v (a i)) := by
  have h := abv_root_le v hm a x hx
  have h' := (posLog_le_posLog (id (v.nonneg x)) ((le_max_left _ _).trans h)).trans
    (posLog_mul (x := (m:ℝ)) (y := ∏ i, max (v (a i)) 1))
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmEq : log⁺ (m:ℝ) = log m := by rw [posLog_eq_log_max_one (by positivity),max_eq_right hmR]
  rw [hmEq] at h'
  have hprod := posLog_prod univ (fun i => max (v (a i)) 1)
  simp only [posLog_max_one _ (v.nonneg _)] at hprod
  linarith

omit [NumberField K] [IsGalois ℚ K] in
lemma local_nonarch_posLog_root (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    {m : ℕ} (hm : 0 < m) (a : Fin m → K) (x : K)
    (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    log⁺ (v x) ≤ ∑ i, log⁺ (v (a i)) := by
  have h := nonarch_root_le v hv hm a x hx
  have h' := (posLog_le_posLog (id (v.nonneg x)) ((le_max_left _ _).trans h)).trans
    (posLog_prod univ (fun i => max (v (a i)) 1))
  simpa only [posLog_max_one _ (v.nonneg _)] using h'

omit [IsGalois ℚ K] in
lemma exactHeight_root_le {m : ℕ} (hm : 0 < m) (a : Fin m → K) (x : K)
    (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    exactHeight K x ≤ log m + ∑ i, exactHeight K (a i) := by
  have harch : (∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ x)) ≤
      (Module.finrank ℚ K : ℝ)*log m +
      ∑ i, ∑ σ : K →ₐ[ℚ] ℂ, log⁺ (infiniteEntry K σ (a i)) := by
    calc
      _ ≤ ∑ σ : K →ₐ[ℚ] ℂ, (log m + ∑ i, log⁺ (infiniteEntry K σ (a i))) :=
        sum_le_sum fun σ _ => local_posLog_root K (infiniteEntry K σ) hm a x hx
      _ = _ := by
        rw [sum_add_distrib,sum_comm]
        simp only [sum_const,card_univ,nsmul_eq_mul,infiniteEntry_count]
  have hfin : (∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 x)) ≤
      ∑ i, ∑ᶠ v : Nat.Primes × Gal(K/ℚ), log⁺ (finiteEntry K v.1 v.2 (a i)) := by
    rw [← finsum_sum_comm univ (fun (v : Nat.Primes × Gal(K/ℚ)) (i : Fin m) => log⁺ (finiteEntry K v.1 v.2 (a i)))
      (fun i _ => finite_posLog_support K (a i))]
    apply finsum_le_finsum' (finite_posLog_support K x)
      (Function.HasFiniteSupport.sum (fun i => finite_posLog_support K (a i)) univ)
    intro v
    exact local_nonarch_posLog_root K (finiteEntry K v.1 v.2)
      (finiteEntry_nonarch K v.1 v.2) hm a x hx
  have hh := div_le_div_of_nonneg_right (add_le_add harch hfin) (finrank_pos K).le
  unfold exactHeight
  simp only [add_div,mul_div_cancel_left₀ _ (finrank_pos K).ne',sum_div,sum_add_distrib] at hh ⊢
  linarith

end
end PlanarUnitDistances.WeightedAbsoluteValues

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Radicals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

attribute [instance] RadicalModel.field RadicalModel.charZero

section Construction

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
private theorem tail_independent {a : K} {ds : List K}
    (h : SquareIndependent (a :: ds)) : SquareIndependent ds := by
  intro s hs hn c
  exact h s (hs.cons a) hn c

theorem exists_radicalModel (ds : List K) (h : SquareIndependent ds) :
    Nonempty (RadicalModel ds) := by
  induction ds with
  | nil => exact ⟨emptyModel⟩
  | cons a ds ih =>
    obtain ⟨m⟩ := ih (tail_independent h)
    exact ⟨extendModel h m⟩

end Construction

section Consequences

variable {K : Type u} [Field K] [CharZero K] {ds : List K}

omit [CharZero K] in

theorem SquareIndependent.get_ne_zero (h : SquareIndependent ds) (i : Fin ds.length) :
    ds.get i ≠ 0 := by
  intro hi
  apply h [ds.get i] (List.singleton_sublist.mpr (ds.get_mem i))
    (List.cons_ne_nil _ _) 0
  rw [List.prod_cons, List.prod_nil, mul_one, hi]
  norm_num

omit [CharZero K] in
theorem RadicalModel.root_ne_zero (m : RadicalModel ds) (h : SquareIndependent ds)
    (i : Fin ds.length) : m.roots i ≠ 0 := by
  intro hi
  have hs := m.roots_sq i
  rw [hi, zero_pow (by decide : 2 ≠ 0)] at hs
  exact h.get_ne_zero i (m.incl.injective (by simpa using hs.symm))

omit [CharZero K] in

theorem RadicalModel.linear_relation (m : RadicalModel ds) (h : SquareIndependent ds)
    (c : Fin ds.length → K)
    (hc : ∑ i, m.incl (c i) * m.roots i = 0) : ∀ i, c i = 0 := by
  intro i
  have hdiff :
      (∑ j, (m.incl (c j) * m.roots j -
        m.flips i (m.incl (c j) * m.roots j))) =
      2 * (m.incl (c i) * m.roots i) := by
    calc
      _ = ∑ j : Fin ds.length,
          if i = j then 2 * (m.incl (c i) * m.roots i) else 0 := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases hij : i = j
        · subst j
          simp [m.flips_base, m.flips_roots]
          ring
        · simp [map_mul, m.flips_base, m.flips_roots, hij]
      _ = _ := by simp
  rw [Finset.sum_sub_distrib, ← map_sum, hc, map_zero, sub_self] at hdiff
  have hz : m.incl (c i) * m.roots i = 0 :=
    (mul_eq_zero.mp hdiff.symm).resolve_left (by norm_num)
  have hz' : m.incl (c i) = 0 := (mul_eq_zero.mp hz).resolve_right (m.root_ne_zero h i)
  exact m.incl.injective (by simpa using hz')

end Consequences

section LinearSystem

variable {E L : Type u} [Field E] [Field L]
variable {n : Type v} [Fintype n] [DecidableEq n]

theorem solution_lift_fixed (f : E →+* L) (M : Matrix n n E) (b : n → E)
    (hdet : M.det ≠ 0) (σ : E ≃+* E)
    (hM : ∀ i j, σ (M i j) = M i j) (hb : ∀ i, σ (b i) = b i)
    (x : n → L) (hx : (M.map f).mulVec x = fun i => f (b i)) :
    ∃ y : n → E, (∀ i, f (y i) = x i) ∧ (∀ i, σ (y i) = y i) := by
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨y, hy⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) b
  have hunit' : IsUnit (M.map f) := by
    apply (Matrix.isUnit_iff_isUnit_det (M.map f)).mpr
    change IsUnit (f.mapMatrix M).det
    rw [← f.map_det]
    exact (isUnit_iff_ne_zero.mpr hdet).map f
  have hymap : (M.map f).mulVec (fun i => f (y i)) = fun i => f (b i) := by
    ext i
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
      using congrArg f (congrFun hy i)
  have hyx : (fun i => f (y i)) = x :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit') (hymap.trans hx.symm)
  have hyσ : M.mulVec (fun i => σ (y i)) = b := by
    ext i
    simpa only [Matrix.mulVec, dotProduct, map_sum, map_mul, hM, hb]
      using congrArg σ (congrFun hy i)
  have hfix : (fun i => σ (y i)) = y :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (hyσ.trans hy.symm)
  exact ⟨y, fun i => congrFun hyx i, fun i => congrFun hfix i⟩

theorem unused_sign_equation [CharZero E] (σ : E ≃+* E)
    {B A c t r : E} (hr : r ≠ 0) (hB : σ B = B) (hA : σ A = A)
    (hc : σ c = c) (ht : σ t = t) (hflip : σ r = -r)
    (heq : B - r * A = c - r * t) : A = t := by
  have heq' := congrArg σ heq
  simp only [map_sub, map_mul, hB, hA, hc, ht, hflip] at heq'
  have hz : r * (A - t) = 0 := by linear_combination (heq' - heq) / 2
  exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hr)

end LinearSystem

section PlanarSystem

variable {K L : Type u} [Field K] [CharZero K] [Field L]

theorem planar_radical_forces_scalar (f : K →+* L)
    (d a b c t : Fin 4 → K)
    (hind : SquareIndependent [d 0, d 1, d 2, d 3])
    (r : Fin 4 → L) (hr : ∀ i, r i ^ 2 = f (d i))
    (hrank : a 0 * b 1 - b 0 * a 1 ≠ 0 ∨
      a 0 * b 2 - b 0 * a 2 ≠ 0 ∨ a 1 * b 2 - b 1 * a 2 ≠ 0)
    (x y A : L)
    (heq : ∀ i, f (a i) * x + f (b i) * y - r i * A =
      f (c i) - r i * f (t i)) : A = f (t 3) := by
  obtain ⟨m⟩ := exists_radicalModel _ hind
  obtain ⟨φ, hφbase, hφroot⟩ := m.evaluate L f r (by
    intro i; fin_cases i <;> simpa using hr _)
  let M : Matrix (Fin 3) (Fin 3) m.Carrier :=
    !![m.incl (a 0), m.incl (b 0), -m.roots 0;
       m.incl (a 1), m.incl (b 1), -m.roots 1;
       m.incl (a 2), m.incl (b 2), -m.roots 2]
  let rhs : Fin 3 → m.Carrier :=
    ![m.incl (c 0) - m.roots 0 * m.incl (t 0),
      m.incl (c 1) - m.roots 1 * m.incl (t 1),
      m.incl (c 2) - m.roots 2 * m.incl (t 2)]
  have hdet : M.det ≠ 0 := by
    intro hz
    let coeff : Fin 4 → K :=
      ![a 2 * b 1 - a 1 * b 2, a 0 * b 2 - a 2 * b 0,
        a 1 * b 0 - a 0 * b 1, 0]
    have hrel : ∑ i, m.incl (coeff i) * m.roots i = 0 := by
      have hexp := (Matrix.det_fin_three M).symm.trans hz
      simp [M] at hexp
      simp [Fin.sum_univ_succ, coeff]
      linear_combination hexp
    have hc := m.linear_relation hind coeff hrel
    have h0 := hc 0
    have h1 := hc 1
    have h2 := hc 2
    simp [coeff] at h0 h1 h2
    rcases hrank with hh | hh | hh
    · apply hh; linear_combination -h2
    · apply hh; linear_combination h1
    · apply hh; linear_combination -h0
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  have h31 : (3 : Fin 4) ≠ 1 := by decide
  have h32 : (3 : Fin 4) ≠ 2 := by decide
  have hMf : ∀ i j, m.flips 3 (M i j) = M i j := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [M, m.flips_base, m.flips_roots, h30, h31, h32]
  have hbf : ∀ i, m.flips 3 (rhs i) = rhs i := by
    intro i; fin_cases i <;> simp [rhs, m.flips_base, m.flips_roots, h30, h31, h32]
  have hsol : (M.map φ).mulVec ![x, y, A] = fun i => φ (rhs i) := by
    ext i
    fin_cases i <;>
      simp [M, rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
        hφbase, hφroot] <;>
      first | linear_combination heq 0 | linear_combination heq 1 | linear_combination heq 2
  obtain ⟨v, hv, hfix⟩ := solution_lift_fixed φ M rhs hdet (m.flips 3) hMf hbf
    ![x, y, A] hsol
  have hlast : m.incl (a 3) * v 0 + m.incl (b 3) * v 1 - m.roots 3 * v 2 =
      m.incl (c 3) - m.roots 3 * m.incl (t 3) := by
    apply φ.injective
    simpa [hφbase, hφroot, hv] using heq 3
  have hv2 : v 2 = m.incl (t 3) := unused_sign_equation (m.flips 3)
    (m.root_ne_zero hind 3)
    (by simp [hfix, m.flips_base]) (hfix 2) (m.flips_base 3 (c 3))
    (m.flips_base 3 (t 3)) (by simp [m.flips_roots]) hlast
  have hh := congrArg φ hv2
  simpa [hv, hφbase] using hh

theorem line_radical_forces_scalar (f : K →+* L)
    (d a c t : Fin 3 → K)
    (hind : SquareIndependent [d 0, d 1, d 2])
    (r : Fin 3 → L) (hr : ∀ i, r i ^ 2 = f (d i))
    (ha : a 0 ≠ 0) (h A : L)
    (heq : ∀ i, f (a i) * h - r i * A = f (c i) - r i * f (t i)) :
    A = f (t 2) := by
  obtain ⟨m⟩ := exists_radicalModel _ hind
  obtain ⟨φ, hφbase, hφroot⟩ := m.evaluate L f r (by
    intro i; fin_cases i <;> simpa using hr _)
  let M : Matrix (Fin 2) (Fin 2) m.Carrier :=
    !![m.incl (a 0), -m.roots 0; m.incl (a 1), -m.roots 1]
  let rhs : Fin 2 → m.Carrier :=
    ![m.incl (c 0) - m.roots 0 * m.incl (t 0),
      m.incl (c 1) - m.roots 1 * m.incl (t 1)]
  have hdet : M.det ≠ 0 := by
    intro hz
    let coeff : Fin 3 → K := ![a 1, -a 0, 0]
    have hrel : ∑ i, m.incl (coeff i) * m.roots i = 0 := by
      have hexp := (Matrix.det_fin_two M).symm.trans hz
      simp [M] at hexp
      simp [Fin.sum_univ_succ, coeff]
      linear_combination hexp
    have hc := m.linear_relation hind coeff hrel 1
    apply ha
    simpa [coeff] using hc
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have hMf : ∀ i j, m.flips 2 (M i j) = M i j := by
    intro i j; fin_cases i <;> fin_cases j <;>
      simp [M, m.flips_base, m.flips_roots, h20, h21]
  have hbf : ∀ i, m.flips 2 (rhs i) = rhs i := by
    intro i; fin_cases i <;> simp [rhs, m.flips_base, m.flips_roots, h20, h21]
  have hsol : (M.map φ).mulVec ![h, A] = fun i => φ (rhs i) := by
    ext i
    fin_cases i <;>
      simp [M, rhs, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hφbase, hφroot] <;>
      first | linear_combination heq 0 | linear_combination heq 1
  obtain ⟨v, hv, hfix⟩ := solution_lift_fixed φ M rhs hdet (m.flips 2) hMf hbf
    ![h, A] hsol
  have hlast : m.incl (a 2) * v 0 - m.roots 2 * v 1 =
      m.incl (c 2) - m.roots 2 * m.incl (t 2) := by
    apply φ.injective
    simpa [hφbase, hφroot, hv] using heq 2
  have hv1 : v 1 = m.incl (t 2) := unused_sign_equation (m.flips 2)
    (m.root_ne_zero hind 2)
    (by simp [hfix, m.flips_base]) (hfix 1) (m.flips_base 2 (c 2))
    (m.flips_base 2 (t 2)) (by simp [m.flips_roots]) hlast
  have hh := congrArg φ hv1
  simpa [hv, hφbase] using hh

end PlanarSystem

end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
universe u
variable {K L : Type u} [Field K] [CharZero K] [Field L]

theorem radical_system_impossible (f : K →+* L)
    (d a b c t : Fin 4 → K)
    (hind : SquareIndependent [d 0,d 1,d 2,d 3])
    (r : Fin 4 → L) (hr : ∀ i, r i ^ 2 = f (d i))
    (ha : a 0 ≠ 0) (x y A : L)
    (heq : ∀ i, f (a i)*x+f (b i)*y-r i*A = f (c i)-r i*f (t i))
    (hne : ∀ i, A ≠ f (t i)) : False := by
  classical
  by_cases h : a 0*b 1-b 0*a 1 ≠ 0 ∨ a 0*b 2-b 0*a 2 ≠ 0 ∨ a 1*b 2-b 1*a 2 ≠ 0
  · exact hne 3 (planar_radical_forces_scalar f d a b c t hind r hr h x y A heq)
  · push Not at h
    let ι : Fin 3 → Fin 4 := fun i => i.castSucc
    have hsub : SquareIndependent [d (ι 0),d (ι 1),d (ι 2)] := by
      intro s hs hs0 u
      apply hind s (hs.trans ?_) hs0 u
      exact List.sublist_append_left [d 0,d 1,d 2] [d 3]
    have hprop (i : Fin 3) : a (ι i)*b 0=a 0*b (ι i) := by
      fin_cases i
      · rfl
      · dsimp [ι]; linear_combination -h.1
      · dsimp [ι]; linear_combination -h.2.1
    have hfa : f (a 0) ≠ 0 := by simpa only [map_zero] using f.injective.ne ha
    have hcoef (i : Fin 3) : f (a (ι i))*(f (b 0)/f (a 0))=f (b (ι i)) := by
      rw [← mul_div_assoc, div_eq_iff hfa]
      have hh := congrArg f (hprop i)
      simpa only [map_mul, mul_comm (f (a 0))] using hh
    have heq' (i : Fin 3) : f (a (ι i))*(x+(f (b 0)/f (a 0))*y)-r (ι i)*A =
        f (c (ι i))-r (ι i)*f (t (ι i)) := by
      rw [mul_add, ← mul_assoc, hcoef]
      exact heq (ι i)
    have hh := line_radical_forces_scalar f (d ∘ ι) (a ∘ ι) (c ∘ ι) (t ∘ ι)
      hsub (r ∘ ι) (fun i => hr (ι i)) ha (x+(f (b 0)/f (a 0))*y) A heq'
    exact hne 2 hh
end PlanarUnitDistances.Radicals

namespace UnitDistances.DifferentialSystem

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem logDerivative_factorization (D : Derivation k F F) {g h c l : F}
    (hg : g ≠ 0) (hh : h ≠ 0) (hc : c ≠ 0) (hDc : D c = 0)
    (hl : l = g * h⁻¹ * c) : D l / l = D g / g - D h / h := by
  subst l
  simp only [D.leibniz, D.leibniz_inv, hDc, smul_eq_mul, mul_zero]
  field_simp
  ring

theorem edge_radicand {l L : F} (hl : l ≠ 0) (heq : L = 2 - l - l⁻¹) :
    (l⁻¹ - l) ^ 2 = L * (L - 4) := by
  rw [heq]
  field_simp
  ring

end UnitDistances.DifferentialSystem

namespace UnitDistances.DifferentialSystem
variable {k F : Type*} [Field k] [Field F] [Algebra k F]

theorem differentiated_zw (D : Derivation k F F) {z w a b l : F}
    (hl : l ≠ 0) (heq : (z-a)*(w-b)=2-l-l⁻¹) :
    (w-b)*(D z-D a)+(z-a)*(D w-D b)=(l⁻¹-l)*(D l/l) := by
  have hd := congrArg D heq
  simp only [map_sub, D.leibniz, show D 2=0 from D.map_natCast 2,
    D.leibniz_inv, smul_eq_mul] at hd
  calc
    _ = -D l+l⁻¹^2*D l := by linear_combination hd
    _ = _ := by field_simp; ring
end UnitDistances.DifferentialSystem

namespace PlanarUnitDistances.Radicals
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L] [Algebra k L]

theorem differential_distance_obstruction (D : Derivation k L L) (f : K →+* L)
    (z w : K) (a b da db t : Fin 4 → K) (l : Fin 4 → L) (A : L)
    (hind : SquareIndependent
      (List.ofFn (fun i : Fin 4 => ((z-a i)*(w-b i))*((z-a i)*(w-b i)-4))))
    (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (f z-f (a i))*(f w-f (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (f (a i))=f (da i))
    (hdb : ∀ i, D (f (b i))=f (db i))
    (hlog : ∀ i, D (l i)/l i=A-f (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  let d : Fin 4 → K := fun i => ((z-a i)*(w-b i))*((z-a i)*(w-b i)-4)
  have hind' : SquareIndependent [d 0,d 1,d 2,d 3] := by
    simpa [List.ofFn_succ, Fin.succ, d] using hind
  have hw : w-b 0 ≠ 0 := by
    intro hh
    have h0 := hind'.get_ne_zero (0 : Fin 4)
    simp only [List.get_eq_getElem] at h0
    apply h0
    simp [d, hh]
  apply radical_system_impossible f d (fun i => w-b i) (fun i => z-a i)
    (fun i => (w-b i)*da i+(z-a i)*db i) t hind'
    (fun i => (l i)⁻¹-l i) (fun i => ?_) hw (D (f z)) (D (f w)) A
    (fun i => ?_) (fun i => ?_)
  · have hh := UnitDistances.DifferentialSystem.edge_radicand (hl i) (hdist i)
    simpa only [d, map_mul, map_sub, map_ofNat] using hh
  · have hh := UnitDistances.DifferentialSystem.differentiated_zw D (hl i) (hdist i)
    rw [hda, hdb, hlog] at hh
    simp only [map_add, map_mul, map_sub]
    linear_combination hh
  · intro hh
    have hn := div_ne_zero (hD i) (hl i)
    rw [hlog, hh, sub_self] at hn
    exact hn rfl
end PlanarUnitDistances.Radicals

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Valuations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.Radicals

universe u v

open WithZero Multiplicative

theorem exp_neg_one_ne_square (x : ℤᵐ⁰) : WithZero.exp (-1 : ℤ) ≠ x ^ 2 := by
  intro h
  have h' := congrArg WithZero.log h
  simp only [WithZero.log_exp, WithZero.log_pow, nsmul_eq_mul] at h'
  omega

theorem squareIndependent_of_private_valuations
    {K : Type u} [Field K] {ι : Type v} (is : List ι) (hi : is.Nodup)
    (d : ι → K)
    (hv : ∀ i ∈ is, ∃ v : Valuation K ℤᵐ⁰,
      v (d i) = WithZero.exp (-1 : ℤ) ∧ ∀ j ∈ is, j ≠ i → v (d j) = 1) :
    SquareIndependent (is.map d) := by
  intro s hs hsn c hc
  obtain ⟨js, hj, rfl⟩ := List.sublist_map_iff.mp hs
  cases js with
  | nil => exact hsn rfl
  | cons i js =>
    have hnd := List.nodup_cons.mp (hi.sublist hj)
    have him : i ∈ is := hj.subset (by simp)
    obtain ⟨v, hvi, hvj⟩ := hv i him
    have hone : (js.map (fun j => v (d j))).prod = 1 := by
      apply List.prod_eq_one
      intro a ha
      obtain ⟨j, hjm, rfl⟩ := List.mem_map.mp ha
      exact hvj j (hj.subset (by simp [hjm])) (by
        intro he; exact hnd.1 (he ▸ hjm))
    apply exp_neg_one_ne_square (v c)
    have hh := congrArg v hc
    simpa [map_list_prod, List.map_map, Function.comp_def, hvi, hone] using hh

section RootValuation

open Polynomial IsDedekindDomain

variable {K : Type u} [Field K]

theorem pointValuation_polynomial_of_eval_ne_zero {a : K} {p : K[X]}
    (hp : p.eval a ≠ 0) :
    pointValuation a (algebraMap K[X] (RatFunc K) p) = 1 := by
  apply (HeightOneSpectrum.valuation_eq_one_iff_notMem (pointPrime a)).mpr
  simpa [pointPrime, Ideal.mem_span_singleton, dvd_iff_isRoot, IsRoot] using hp

theorem pointValuation_X_sub_C (a : K) :
    pointValuation a (algebraMap K[X] (RatFunc K) (X - C a)) =
      WithZero.exp (-1 : ℤ) := by
  rw [pointValuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_singleton (pointPrime a) (X_sub_C_ne_zero a) rfl

theorem pointValuation_of_simple_root {a : K} {p : K[X]}
    (hp : p.eval a = 0) (hp' : p.derivative.eval a ≠ 0) :
    pointValuation a (algebraMap K[X] (RatFunc K) p) =
      WithZero.exp (-1 : ℤ) := by
  obtain ⟨q, hq⟩ := (dvd_iff_isRoot.mpr hp : X - C a ∣ p)
  have hq' : q.eval a ≠ 0 := by
    simpa [hq, derivative_mul] using hp'
  rw [hq, map_mul, map_mul, pointValuation_X_sub_C,
    pointValuation_polynomial_of_eval_ne_zero hq', mul_one]

theorem squareIndependent_of_private_simple_roots {ι : Type v}
    (is : List ι) (hi : is.Nodup) (d : ι → K[X])
    (h : ∀ i ∈ is, ∃ a : K, (d i).eval a = 0 ∧
      (d i).derivative.eval a ≠ 0 ∧ ∀ j ∈ is, j ≠ i → (d j).eval a ≠ 0) :
    SquareIndependent (is.map (fun i => algebraMap K[X] (RatFunc K) (d i))) := by
  apply squareIndependent_of_private_valuations is hi
  intro i him
  obtain ⟨a, hai, hai', haj⟩ := h i him
  exact ⟨pointValuation a, pointValuation_of_simple_root hai hai',
    fun j hj hji => pointValuation_polynomial_of_eval_ne_zero (haj j hj hji)⟩

end RootValuation

section Plane

open Polynomial

variable {K : Type u} [Field K] [CharZero K]

omit [CharZero K] in
lemma ratFunc_X_sub_C_ne_zero (a : K) :
    (RatFunc.X : RatFunc K) - RatFunc.C a ≠ 0 := by
  simpa using RatFunc.algebraMap_ne_zero (X_sub_C_ne_zero a)

lemma planePrivateRoot_ne_constant (a b c : K) :
    planePrivateRoot a b ≠ RatFunc.C c := by
  intro h
  have he := (div_eq_iff (ratFunc_X_sub_C_ne_zero a)).mp h
  have hp : C b * (X - C a) + 4 = C c * (X - C a) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, map_sub, map_add, map_ofNat, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] using he
  have hp' := congrArg (Polynomial.eval a) hp
  norm_num at hp'

lemma planePrivateRoot_injective :
    Function.Injective (fun ab : K × K => planePrivateRoot ab.1 ab.2) := by
  intro ab cd he
  change planePrivateRoot ab.1 ab.2 = planePrivateRoot cd.1 cd.2 at he
  have hc := (div_eq_div_iff (ratFunc_X_sub_C_ne_zero ab.1)
    (ratFunc_X_sub_C_ne_zero cd.1)).mp he
  have hp : (C ab.2 * (X - C ab.1) + 4) * (X - C cd.1) =
      (C cd.2 * (X - C cd.1) + 4) * (X - C ab.1) := by
    apply RatFunc.algebraMap_injective K
    simpa only [map_mul, map_sub, map_add, map_ofNat, RatFunc.algebraMap_C,
      RatFunc.algebraMap_X] using hc
  have hp' := congrArg (Polynomial.eval ab.1) hp
  simp only [eval_mul, eval_add, eval_sub, eval_C, eval_X, eval_ofNat,
    sub_self, mul_zero, zero_add] at hp'
  have ha : ab.1 = cd.1 := by
    have h4 : (4 : K) ≠ 0 := by norm_num
    exact sub_eq_zero.mp ((mul_eq_zero.mp hp').resolve_left h4)
  have hb : ab.2 = cd.2 := by
    unfold planePrivateRoot at he
    rw [ha] at he
    have hh := (div_left_inj' (ratFunc_X_sub_C_ne_zero cd.1)).mp he
    exact RatFunc.C_injective (mul_right_cancel₀ (ratFunc_X_sub_C_ne_zero cd.1)
      (add_right_cancel hh))
  exact Prod.ext ha hb

omit [CharZero K] in
lemma planePrivateRoot_distance (a b : K) :
    (planeDistancePoly a b).eval (planePrivateRoot a b) = 4 := by
  simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X, planePrivateRoot]
  field_simp [ratFunc_X_sub_C_ne_zero a]
  ring

lemma planePrivateRoot_simple (a b : K) :
    (planeRadicandPoly a b).eval (planePrivateRoot a b) = 0 ∧
    (planeRadicandPoly a b).derivative.eval (planePrivateRoot a b) ≠ 0 := by
  constructor
  · simp [planeRadicandPoly, planePrivateRoot_distance]
  · have h4 : (4 : RatFunc K) ≠ 0 := by norm_num
    have hd : (planeDistancePoly a b).derivative = C (RatFunc.X - RatFunc.C a) := by
      simp [planeDistancePoly]
    simpa [planeRadicandPoly, derivative_mul, derivative_sub,
      planePrivateRoot_distance, hd] using
      mul_ne_zero h4 (ratFunc_X_sub_C_ne_zero a)

lemma planePrivateRoot_other (ab cd : K × K) (h : cd ≠ ab) :
    (planeRadicandPoly cd.1 cd.2).eval (planePrivateRoot ab.1 ab.2) ≠ 0 := by
  simp only [planeRadicandPoly, eval_mul, eval_sub, eval_ofNat, mul_ne_zero_iff]
  constructor
  · simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X, mul_ne_zero_iff]
    exact ⟨ratFunc_X_sub_C_ne_zero cd.1,
      sub_ne_zero.mpr (planePrivateRoot_ne_constant ab.1 ab.2 cd.2)⟩
  · intro he
    have hd := sub_eq_zero.mp he
    have hroot : planePrivateRoot ab.1 ab.2 = planePrivateRoot cd.1 cd.2 := by
      apply (eq_div_iff (ratFunc_X_sub_C_ne_zero cd.1)).mpr
      simp only [planeDistancePoly, eval_mul, eval_C, eval_sub, eval_X] at hd
      linear_combination hd
    exact h (planePrivateRoot_injective hroot).symm

theorem plane_radicands_squareIndependent (centers : List (K × K))
    (h : centers.Nodup) :
    SquareIndependent (centers.map (fun ab =>
      algebraMap (RatFunc K)[X] (RatFunc (RatFunc K))
        (planeRadicandPoly ab.1 ab.2))) := by
  apply squareIndependent_of_private_simple_roots centers h
  intro ab hab
  exact ⟨planePrivateRoot ab.1 ab.2, (planePrivateRoot_simple ab.1 ab.2).1,
    (planePrivateRoot_simple ab.1 ab.2).2,
    fun cd _ hcd => planePrivateRoot_other ab cd hcd⟩

end Plane

end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.GenericCurve
open Polynomial
open scoped nonZeroDivisors
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

lemma ratEval_polynomial (z : U) (hz : Transcendental K z) (p : K[X]) :
    ratEval z hz (algebraMap K[X] (RatFunc K) p) = aeval z p := by
  change IsFractionRing.lift (transcendental_iff_injective.mp hz)
    (algebraMap K[X] (RatFunc K) p) = _
  exact IsFractionRing.lift_algebraMap _ p

@[simp] lemma ratEval_X (z : U) (hz : Transcendental K z) :
    ratEval z hz RatFunc.X=z := by
  simpa only [RatFunc.algebraMap_X,aeval_X] using ratEval_polynomial z hz (X : K[X])

@[simp] lemma ratEval_C (z : U) (hz : Transcendental K z) (a : K) :
    ratEval z hz (RatFunc.C a)=algebraMap K U a := by
  simpa only [RatFunc.algebraMap_C,aeval_C] using ratEval_polynomial z hz (C a)

end PlanarUnitDistances.GenericCurve

namespace PlanarUnitDistances.GenericPlane
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

theorem exists_plane_embedding (x : Fin 2 → U) (hx : AlgebraicIndependent K x) :
    ∃ f : RatFunc (RatFunc K) →+* U,
      f (RatFunc.X : RatFunc (RatFunc K)) = x 1 ∧
      f (RatFunc.C (RatFunc.X : RatFunc K)) = x 0 ∧
      ∀ a : K, f (RatFunc.C (RatFunc.C a)) = algebraMap K U a := by
  let E := IntermediateField.adjoin K ({x 0} : Set U)
  let z : E := ⟨x 0, IntermediateField.subset_adjoin K _ (Set.mem_singleton _)⟩
  have hz : Transcendental K z := by
    intro h
    exact hx.transcendental 0 (h.algHom E.val)
  have hw : Transcendental E (x 1) := by
    apply IntermediateField.transcendental_adjoin_iff.mpr
    have hh := hx.transcendental_adjoin (s := {(0 : Fin 2)}) (i := 1) (by decide)
    rw [Set.image_singleton] at hh
    exact hh
  let g : RatFunc K →ₐ[K] E := GenericCurve.ratEval z hz
  let φ : (RatFunc K)[X] →+* U := (aeval (x 1) : E[X] →ₐ[E] U).toRingHom.comp
    (Polynomial.mapRingHom g.toRingHom)
  have hφ : Function.Injective φ :=
    (transcendental_iff_injective.mp hw).comp (Polynomial.map_injective g.toRingHom g.injective)
  let f : RatFunc (RatFunc K) →+* U := IsFractionRing.lift hφ
  have hf (p : (RatFunc K)[X]) : f (algebraMap (RatFunc K)[X] _ p)=φ p :=
    IsFractionRing.lift_algebraMap hφ p
  refine ⟨f, ?_, ?_, ?_⟩
  · rw [← RatFunc.algebraMap_X, hf]
    simp [φ]
  · rw [← RatFunc.algebraMap_C, hf]
    change aeval (x 1) ((C RatFunc.X).map g.toRingHom) = x 0
    rw [Polynomial.map_C, aeval_C]
    change (g RatFunc.X : U) = x 0
    simp [g,z]
  · intro a
    rw [← RatFunc.algebraMap_C, hf]
    change aeval (x 1) ((C (RatFunc.C a)).map g.toRingHom) = algebraMap K U a
    rw [Polynomial.map_C, aeval_C]
    change (g (RatFunc.C a) : U) = algebraMap K U a
    simp [g]
end PlanarUnitDistances.GenericPlane

namespace PlanarUnitDistances.Radicals
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L]
  [Algebra k L] [Algebra K L]

theorem plane_differential_obstruction (D : Derivation k L L)
    (x : Fin 2 → L) (hx : AlgebraicIndependent K x)
    (a b da db t : Fin 4 → K) (hab : Function.Injective (fun i => (a i,b i)))
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (x 0-algebraMap K L (a i))*(x 1-algebraMap K L (b i))=
      2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  obtain ⟨f,hw,hz,hc⟩ := GenericPlane.exists_plane_embedding x hx
  let C : K →+* RatFunc (RatFunc K) := RatFunc.C.comp RatFunc.C
  have hC (q : K) : f (C q)=algebraMap K L q := hc q
  have hind := plane_radicands_squareIndependent (List.ofFn (fun i => (a i,b i)))
    (List.nodup_ofFn.mpr hab)
  have hind' : SquareIndependent (List.ofFn (fun i : Fin 4 =>
      ((RatFunc.C (RatFunc.X : RatFunc K)-C (a i))*(RatFunc.X-C (b i)))*
      ((RatFunc.C (RatFunc.X : RatFunc K)-C (a i))*(RatFunc.X-C (b i))-4))) := by
    simpa only [List.map_ofFn, planeRadicandPoly, planeDistancePoly,
      map_mul, map_sub, map_ofNat, RatFunc.algebraMap_C, RatFunc.algebraMap_X,
      Function.comp_def, C, RingHom.comp_apply] using hind
  apply differential_distance_obstruction D f (RatFunc.C RatFunc.X) RatFunc.X
    (C ∘ a) (C ∘ b) (C ∘ da) (C ∘ db) (C ∘ t) l A hind' hl
  · intro i; simpa only [hz,hw,Function.comp_apply,hC] using hdist i
  · intro i; simpa only [Function.comp_apply,hC] using hda i
  · intro i; simpa only [Function.comp_apply,hC] using hdb i
  · intro i; simpa only [Function.comp_apply,hC] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Derivations
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.BivariateDegree
open Polynomial
variable {K : Type*} [Field K]
attribute [local instance] Classical.propDecidable

lemma size_mul {f g : K[X][X]} (hf : f ≠ 0) (hg : g ≠ 0) :
    size (f*g)=size f+size g := by
  unfold size
  have hf' : Bivariate.swap f ≠ 0 := fun h => hf (Bivariate.swap.injective (h.trans (map_zero _).symm))
  have hg' : Bivariate.swap g ≠ 0 := fun h => hg (Bivariate.swap.injective (h.trans (map_zero _).symm))
  rw [natDegree_mul hf hg,map_mul,natDegree_mul hf' hg']
  omega

lemma size_eq_zero_iff (f : K[X][X]) : size f=0 ↔ ∃ c : K,f=C (C c) := by
  constructor
  · intro hs
    have hs' : f.natDegree+(Bivariate.swap f).natDegree=0 := hs
    have hd : f.natDegree=0 := by omega
    obtain ⟨p,hp⟩ := natDegree_eq_zero.mp hd
    subst f
    have hd' : p.natDegree=0 := by
      simpa only [size,Bivariate.swap_C,natDegree_C,zero_add,
        natDegree_map_eq_of_injective C_injective] using hs
    obtain ⟨c,hc⟩ := natDegree_eq_zero.mp hd'
    exact ⟨c,by rw [← hc]⟩
  · rintro ⟨c,rfl⟩
    simp only [size,natDegree_C,Bivariate.swap_C_C,Nat.add_zero]

lemma size_pos_iff (f : K[X][X]) (hf : f ≠ 0) : 0<size f ↔ ¬ IsUnit f := by
  rw [Nat.pos_iff_ne_zero,not_iff_not,size_eq_zero_iff]
  constructor
  · rintro ⟨c,rfl⟩
    apply isUnit_C.mpr
    apply isUnit_C.mpr
    exact isUnit_iff_ne_zero.mpr (by simpa using hf)
  · intro hh
    obtain ⟨p,hp,hpe⟩ := isUnit_iff.mp hh
    obtain ⟨c,hc,hce⟩ := isUnit_iff.mp hp
    exact ⟨c,by rw [← hpe,← hce]⟩

theorem irreducible_zero_capture {α : Type*} (S : Finset α) (z w : α → K)
    (f : K[X][X]) (hf : f ≠ 0) (hnu : ¬IsUnit f) :
    ∃ g : K[X][X], Irreducible g ∧ g ∣ f ∧ size g ≤ size f ∧
    (S.filter (fun a => f.eval₂ (evalRingHom (z a)) (w a)=0)).card ≤
      size f*(S.filter (fun a => g.eval₂ (evalRingHom (z a)) (w a)=0)).card := by
  classical
  generalize hd : size f=d
  induction d using Nat.strong_induction_on generalizing f with
  | h d ih =>
    by_cases hi : Irreducible f
    · refine ⟨f,hi,dvd_refl _,hd.le,?_⟩
      have hs := (size_pos_iff f hf).mpr hnu
      rw [hd] at hs
      exact Nat.le_mul_of_pos_left _ hs
    · obtain ⟨g,h,hfgh,hgnu,hhnu⟩ : ∃ g h, f=g*h ∧ ¬IsUnit g ∧ ¬IsUnit h := by
        simpa [irreducible_iff,hnu] using hi
      have hg : g ≠ 0 := left_ne_zero_of_mul (hfgh ▸ hf)
      have hh : h ≠ 0 := right_ne_zero_of_mul (hfgh ▸ hf)
      have hsz : size g+size h=d := by rw [← size_mul hg hh,← hfgh,hd]
      have hgp := (size_pos_iff g hg).mpr hgnu
      have hhp := (size_pos_iff h hh).mpr hhnu
      obtain ⟨g',hgi,hgd,hgs,hgc⟩ := ih (size g) (by omega) g hg hgnu rfl
      obtain ⟨h',hhi,hhd,hhs,hhc⟩ := ih (size h) (by omega) h hh hhnu rfl
      let Z (p : K[X][X]) := S.filter fun a => p.eval₂ (evalRingHom (z a)) (w a)=0
      have hc : (Z f).card ≤ (Z g).card+(Z h).card := by
        apply (Finset.card_le_card (t := Z g ∪ Z h) ?_).trans (Finset.card_union_le _ _)
        intro a ha
        simp only [Z,Finset.mem_filter,Finset.mem_union,hfgh,eval₂_mul,mul_eq_zero] at ha ⊢
        aesop
      rcases le_total (Z g').card (Z h').card with hle|hle
      · refine ⟨h',hhi,hhd.trans (hfgh ▸ dvd_mul_left h g),hhs.trans ?_,?_⟩
        · omega
        · change (Z f).card ≤ d*(Z h').card
          rw [← hsz,add_mul]
          exact hc.trans (Nat.add_le_add (hgc.trans (Nat.mul_le_mul_left _ hle)) hhc)
      · refine ⟨g',hgi,hgd.trans (hfgh ▸ dvd_mul_right g h),hgs.trans ?_,?_⟩
        · omega
        · change (Z f).card ≤ d*(Z g').card
          rw [← hsz,add_mul]
          exact hc.trans (Nat.add_le_add hgc (hhc.trans (Nat.mul_le_mul_left _ hle)))

end PlanarUnitDistances.BivariateDegree

namespace UnitDistances.DerivationObstruction

open TensorProduct

section Fields
variable {k F : Type*} [Field k] [Field F] [Algebra k F] [CharZero k]

theorem exists_derivation_basis_one {ι : Type*} (b : ι → F)
    (hb : IsTranscendenceBasis k b) (i : ι) :
    ∃ d : Derivation k F F, d (b i) = 1 := by
  classical
  let P := MvPolynomial ι k
  let Q := FractionRing P
  let E := IntermediateField.adjoin k (Set.range b)
  let e : Q ≃ₐ[k] E := hb.1.aevalEquivField
  let f : Q →ₐ[k] F := E.val.comp e.toAlgHom
  let : Algebra Q F := f.toRingHom.toAlgebra
  have : IsScalarTower k Q F := IsScalarTower.of_algebraMap_eq fun x => by
    exact (f.commutes x).symm
  have : Algebra.IsAlgebraic E F := hb.isAlgebraic_field
  have : Algebra.IsAlgebraic Q F :=
    Algebra.IsAlgebraic.of_ringHom_of_comp_eq e.toRingHom (RingHom.id F)
      e.surjective Function.injective_id rfl
  have : CharZero Q := inferInstance
  have : Algebra.FormallyEtale Q F := Algebra.FormallyEtale.of_isSeparable Q F
  let dP : Derivation k P Q := MvPolynomial.mkDerivation k (fun j => if j = i then 1 else 0)
  let dQ : Derivation k Q Q := extendDerivation dP
  let dQF : Derivation k Q F := (Algebra.linearMap Q F).compDer dQ
  refine ⟨extendDerivation dQF, ?_⟩
  have hbi : algebraMap Q F (algebraMap P Q (MvPolynomial.X i)) = b i := by
    change (e (algebraMap P Q (MvPolynomial.X i)) : F) = b i
    rw [AlgebraicIndependent.aevalEquivField_algebraMap_apply_coe]
    simp
  rw [← hbi, extendDerivation_algebraMap]
  change algebraMap Q F (extendDerivation dP
    (algebraMap P Q (MvPolynomial.X i))) = 1
  rw [extendDerivation_algebraMap]
  have heval : dP (MvPolynomial.X i) = 1 := by
    change MvPolynomial.mkDerivation k (fun j => if j = i then (1 : Q) else 0)
      (MvPolynomial.X i) = 1
    rw [MvPolynomial.mkDerivation_X]
    simp
  rw [heval, map_one]

theorem exists_derivation_one {x : F} (hx : Transcendental k x) :
    ∃ d : Derivation k F F, d x = 1 := by
  have hs : AlgebraicIndepOn k id ({x} : Set F) := by
    apply (algebraicIndependent_singleton_iff ⟨x, by simp⟩).mpr
    exact hx
  obtain ⟨b, hxb, hb⟩ := exists_isTranscendenceBasis_superset hs
  exact exists_derivation_basis_one Subtype.val hb ⟨x, hxb (by simp)⟩

theorem exists_common_derivation {ι : Type*} [Finite ι] (x : ι → F)
    (hx : ∀ i, Transcendental k (x i)) :
    ∃ d : Derivation k F F, ∀ i, d (x i) ≠ 0 := by
  have : CharZero F := Algebra.charZero_of_charZero k F
  let ev (i : ι) : Module.Dual F (Derivation k F F) :=
    { toFun := fun d => d (x i)
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  apply Module.Dual.exists_forall_ne_zero_of_forall_exists ev
  intro i
  obtain ⟨d, hd⟩ := exists_derivation_one (hx i)
  exact ⟨d, by change d (x i) ≠ 0; rw [hd]; exact one_ne_zero⟩

end Fields

end UnitDistances.DerivationObstruction

namespace PlanarUnitDistances.GridDerivation
universe u
variable {k U : Type u} [Field k] [CharZero k] [Field U] [Algebra k U]

theorem exists_derivation_log (l : Fin 21 → Fin 4 → U)
    (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k,
      l i j*l 0 0=l i 0*l 0 j*algebraMap k U c) :
    ∃ D : Derivation k U U, ∃ A : Fin 21 → U, ∃ t : Fin 4 → U,
      (∀ i j, D (l i j)≠0) ∧ (∀ i j, D (l i j)/l i j=A i-t j) := by
  have hl (i j) : l i j≠0 := fun h => htrans i j (h ▸ isAlgebraic_zero)
  obtain ⟨D,hD⟩ := UnitDistances.DerivationObstruction.exists_common_derivation
    (fun ij : Fin 21 × Fin 4 => l ij.1 ij.2) (fun ij => htrans ij.1 ij.2)
  let h : Fin 4 → U := fun j => l 0 0 / l 0 j
  refine ⟨D,(fun i => D (l i 0)/l i 0),(fun j => D (h j)/h j),(fun i j => hD (i,j)),?_⟩
  intro i j
  obtain ⟨c,hc⟩ := hrect i j
  have hc0 : algebraMap k U c≠0 := by
    intro he
    rw [he,mul_zero] at hc
    exact mul_ne_zero (hl i j) (hl 0 0) hc
  apply UnitDistances.DifferentialSystem.logDerivative_factorization D
    (hl i 0) (div_ne_zero (hl 0 0) (hl 0 j)) hc0 (D.map_algebraMap c)
  change l i j = l i 0 * (l 0 0 / l 0 j)⁻¹ * algebraMap k U c
  field_simp [hl 0 0,hl 0 j]
  linear_combination hc
end PlanarUnitDistances.GridDerivation

namespace UnitDistanceSurvival
open Set

lemma free_subset {α : Type*} (M : Matroid α) (I C : Set α)
    (hI : M.Indep I) (hIf : I.Finite) (hCf : C.Finite) (hC : C ⊆ M.E) :
    ∃ B D : Set α, M.IsBasis B C ∧ D ⊆ I ∧ Disjoint D C ∧
      M.Indep (D ∪ B) ∧ (I \ D).ncard ≤ C.ncard := by
  obtain ⟨B, hB⟩ := M.exists_isBasis C hC
  obtain ⟨J, hJ, hJB⟩ := hB.exists_isBasis_inter_eq_of_superset
    (Y := I ∪ C) subset_union_right (union_subset hI.subset_ground hC)
  have hJf : J.Finite := (hIf.union hCf).subset hJ.subset
  have hBf : B.Finite := hCf.subset hB.subset
  have hDI : J \ C ⊆ I := by
    intro a ha
    exact (hJ.subset ha.1).resolve_right ha.2
  have hIJcard : I.ncard ≤ J.ncard := by
    have h := hI.encard_le_eRk_of_subset (X := I ∪ C) subset_union_left
    rw [← hJ.encard_eq_eRk, ← hIf.cast_ncard_eq, ← hJf.cast_ncard_eq] at h
    exact_mod_cast h
  have hcardJ : (J \ C).ncard + B.ncard = J.ncard := by
    have h := Set.encard_sdiff_add_encard_inter J C
    rw [hJB, ← (hJf.sdiff).cast_ncard_eq, ← hBf.cast_ncard_eq,
      ← hJf.cast_ncard_eq] at h
    exact_mod_cast h
  have hcardI : (I \ (J \ C)).ncard + (J \ C).ncard = I.ncard := by
    simpa only [union_eq_self_of_subset_right hDI] using
      Set.ncard_sdiff_add_ncard I (J \ C) hIf hJf.sdiff
  refine ⟨B, J \ C, hB, hDI, disjoint_sdiff_left, ?_, ?_⟩
  · convert hJ.indep using 1
    rw [← hJB, sdiff_union_inter]
  · have := Set.ncard_le_ncard hB.subset hCf
    omega

lemma surviving_block {α : Type*} (M : Matroid α) {ι δ : Type*} [Fintype ι] [Fintype δ]
    (x : ι × δ → α) (hx : Function.Injective x)
    (hind : M.Indep (Set.range x)) (C : Set α) (hCf : C.Finite)
    (hC : C ⊆ M.E) (hcard : C.ncard < Fintype.card ι) :
    ∃ i : ι, ∃ B : Set α, M.IsBasis B C ∧
      Disjoint (Set.range (fun j : δ => x (i,j))) B ∧
      M.Indep (Set.range (fun j : δ => x (i,j)) ∪ B) := by
  classical
  obtain ⟨B,D,hB,hDI,hDC,hDB,hsmall⟩ :=
    free_subset M (Set.range x) C hind (Set.finite_range x) hCf hC
  have hex : ∃ i : ι, ∀ j : δ, x (i,j) ∈ D := by
    by_contra hn
    push Not at hn
    choose j hj using hn
    let f : ι → ↥(Set.range x \ D) := fun i => ⟨x (i,j i), ⟨⟨(i,j i),rfl⟩,hj i⟩⟩
    have hf : Function.Injective f := by
      intro i i' h
      have hh := hx (congrArg Subtype.val h)
      exact congrArg Prod.fst hh
    let : Fintype ↥(Set.range x \ D) := (Set.finite_range x).sdiff.fintype
    have hc := Fintype.card_le_of_injective f hf
    have hncard : Fintype.card ↥(Set.range x \ D) = (Set.range x \ D).ncard := by
      exact Set.fintypeCard_eq_ncard _
    rw [hncard] at hc
    omega
  obtain ⟨i,hi⟩ := hex
  have hRD : Set.range (fun j : δ => x (i,j)) ⊆ D := by
    rintro a ⟨j,rfl⟩
    exact hi j
  refine ⟨i,B,hB,?_,hDB.subset (union_subset_union_left B hRD)⟩
  exact (hDC.mono hRD hB.subset)

lemma independent_over_basis {F K δ : Type*} [Field F] [Field K] [Algebra F K]
    (x : δ → K) (hx : Function.Injective x) (B C : Set K)
    (hB : (AlgebraicIndependent.matroid F K).IsBasis B C)
    (hd : Disjoint (Set.range x) B)
    (hu : (AlgebraicIndependent.matroid F K).Indep (Set.range x ∪ B)) :
    AlgebraicIndependent (algebraicClosure (IntermediateField.adjoin F C) K) x := by
  let f : δ ⊕ B → ↥(Set.range x ∪ B) := Sum.elim
    (fun j => ⟨x j, Or.inl ⟨j,rfl⟩⟩) (fun b => ⟨b,Or.inr b.2⟩)
  have hf : Function.Injective f := by
    intro a b h
    cases a with
    | inl a =>
      cases b with
      | inl b => exact congrArg Sum.inl (hx (congrArg Subtype.val h))
      | inr b =>
        exfalso
        have h' : x a = (b : K) := congrArg Subtype.val h
        exact Set.disjoint_left.mp hd ⟨a,rfl⟩ (h'.symm ▸ b.2)
    | inr a =>
      cases b with
      | inl b =>
        exfalso
        have h' : (a : K) = x b := congrArg Subtype.val h
        exact Set.disjoint_left.mp hd ⟨b,rfl⟩ (h' ▸ a.2)
      | inr b =>
        have h' : (a : K) = (b : K) :=
          congrArg (fun z : ↥(Set.range x ∪ B) => (z : K)) h
        exact congrArg Sum.inr (Subtype.ext h')
  have hg : AlgebraicIndependent F (Sum.elim x (fun b : B => (b : K))) := by
    convert hu.comp f hf using 1
    funext u
    cases u <;> rfl
  have hb := (AlgebraicIndependent.sumElim_iff.mp hg).2
  rw [Subtype.range_coe] at hb
  have hbf : AlgebraicIndependent (IntermediateField.adjoin F B) x :=
    IntermediateField.algebraicIndependent_adjoin_iff.mpr hb
  have hBC : IntermediateField.adjoin F B ≤ IntermediateField.adjoin F C :=
    IntermediateField.adjoin_le_iff.mpr fun a ha =>
      IntermediateField.subset_adjoin F C (hB.subset ha)
  let : Algebra (IntermediateField.adjoin F B) (IntermediateField.adjoin F C) :=
    (IntermediateField.inclusion hBC).toAlgebra
  let : IsScalarTower (IntermediateField.adjoin F B)
      (IntermediateField.adjoin F C) K :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have halg : ∀ a ∈ C, IsAlgebraic (IntermediateField.adjoin F B) a := by
    intro a ha
    exact IntermediateField.isAlgebraic_adjoin_iff.mpr
      ((AlgebraicIndependent.matroid_isBasis_iff.mp hB).2.2 a ha)
  let : Algebra.IsAlgebraic (IntermediateField.adjoin F B)
      (IntermediateField.adjoin F C) := by
    refine ⟨fun a => (isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom (IntermediateField.adjoin F B)
        (IntermediateField.adjoin F C) K) Subtype.val_injective).mp ?_⟩
    rcases a with ⟨a,ha⟩
    change IsAlgebraic (IntermediateField.adjoin F B) a
    induction ha using IntermediateField.adjoin_induction with
    | mem x hx => exact halg x hx
    | algebraMap a =>
      exact isAlgebraic_algebraMap (⟨algebraMap F K a,
        IntermediateField.algebraMap_mem _ a⟩ : IntermediateField.adjoin F B)
    | add x y hx hy hx' hy' => exact hx'.add hy'
    | inv x hx hx' => exact hx'.inv
    | mul x y hx hy hx' hy' => exact hx'.mul hy'
  exact (hbf.extendScalars (IntermediateField.adjoin F C)).algebraicClosure

theorem survives_algebraic_closure {F K ι δ κ : Type*}
    [Field F] [Field K] [Algebra F K]
    [Fintype ι] [Fintype δ] [Fintype κ]
    (x : ι × δ → K) (hx : AlgebraicIndependent F x) (y : κ → K)
    (hcard : Fintype.card κ < Fintype.card ι) :
    ∃ i : ι, AlgebraicIndependent
      (algebraicClosure (IntermediateField.adjoin F (Set.range y)) K)
        (fun j : δ => x (i,j)) := by
  classical
  have hcle : (Set.range y).ncard ≤ Fintype.card κ := by
    simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using
      (Set.ncard_image_le (s := Set.univ) (f := y))
  have hc : (Set.range y).ncard < Fintype.card ι := lt_of_le_of_lt hcle hcard
  obtain ⟨i,B,hB,hd,hu⟩ := surviving_block (AlgebraicIndependent.matroid F K)
    x hx.injective hx.coe_range (Set.range y) (Set.finite_range y)
    (by simp) hc
  refine ⟨i,independent_over_basis _ ?_ B (Set.range y) hB hd hu⟩
  intro a b h
  exact congrArg Prod.snd (hx.injective h)

end UnitDistanceSurvival

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Grid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.CoefficientField
universe u
variable {B U : Type u} [Field B] [Field U] [Algebra B U]

theorem exists_left_block {δ : Type*} [Fintype δ]
    (x : Fin 21 × δ → U) (hx : AlgebraicIndependent B x)
    (y : Fin 4 × Fin 5 → U) :
    ∃ i : Fin 21, AlgebraicIndependent (FieldOf (B := B) y) (fun j => x (i,j)) :=
  UnitDistanceSurvival.survives_algebraic_closure x hx y (by decide)

end PlanarUnitDistances.CoefficientField

namespace PlanarUnitDistances.GridObstruction
open CoefficientField
universe u
variable {k B U : Type u} [Field k] [CharZero k] [Field B] [CharZero B]
  [Field U] [Algebra k U] [Algebra B U]

theorem plane (x : Fin 21 × Fin 2 → U) (hx : AlgebraicIndependent B x)
    (a b : Fin 4 → U) (hab : Function.Injective (fun j => (a j,b j)))
    (l : Fin 21 → Fin 4 → U) (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k, l i j*l 0 0=l i 0*l 0 j*algebraMap k U c)
    (hdist : ∀ i j, (x (i,0)-a j)*(x (i,1)-b j)=2-l i j-(l i j)⁻¹) : False := by
  obtain ⟨D,A,t,hD,hlog⟩ := GridDerivation.exists_derivation_log l htrans hrect
  let y := parameters D a b t
  let K := FieldOf (B := B) y
  let a' : Fin 4 → K := fun j => entry y (j,0)
  let b' : Fin 4 → K := fun j => entry y (j,1)
  let da' : Fin 4 → K := fun j => entry y (j,2)
  let db' : Fin 4 → K := fun j => entry y (j,3)
  let t' : Fin 4 → K := fun j => entry y (j,4)
  have ha' (j) : algebraMap K U (a' j)=a j := rfl
  have hb' (j) : algebraMap K U (b' j)=b j := rfl
  have hda' (j) : algebraMap K U (da' j)=D (a j) := rfl
  have hdb' (j) : algebraMap K U (db' j)=D (b j) := rfl
  have ht' (j) : algebraMap K U (t' j)=t j := rfl
  obtain ⟨i,hi⟩ := exists_left_block x hx y
  apply Radicals.plane_differential_obstruction D (fun j => x (i,j)) hi
    a' b' da' db' t' ?_ (l i) (A i) ?_ ?_ ?_ ?_ ?_ (hD i)
  · intro j j' he
    apply hab
    have hh := congrArg (fun q : K × K => (algebraMap K U q.1,algebraMap K U q.2)) he
    simpa only [ha',hb'] using hh
  · intro j h
    exact htrans i j (h ▸ isAlgebraic_zero)
  · intro j
    rw [ha',hb']
    exact hdist i j
  · intro j
    rw [ha',hda']
  · intro j
    rw [hb',hdb']
  · intro j
    rw [ht']
    exact hlog i j
end PlanarUnitDistances.GridObstruction

namespace UnitDistances.UltraField
open Filter

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i, Field (K i)]

noncomputable instance instIsAlgClosedFieldProduct [∀ i, IsAlgClosed (K i)] : IsAlgClosed (FieldProduct U K) := by
  classical
  apply IsAlgClosed.of_exists_root
  intro p hp hirr
  obtain ⟨q, hq⟩ := Polynomial.map_surjective (mk U K)
    Ideal.Quotient.mk_surjective p
  have hn : 0 < p.natDegree :=
    Polynomial.natDegree_pos_iff_degree_pos.mpr (Polynomial.degree_pos_of_irreducible hirr)
  have hc : mk U K (q.coeff p.natDegree) ≠ 0 := by
    rw [← Polynomial.coeff_map, hq, Polynomial.coeff_natDegree, hp.leadingCoeff]
    exact one_ne_zero
  have hev : ∀ᶠ i in U, q.coeff p.natDegree i ≠ 0 :=
    Ultrafilter.eventually_not.mpr ((mk_eq_zero U K _).not.mp hc)
  have hroot : ∀ᶠ i in U, ∃ x : K i,
      (q.map (Pi.evalRingHom K i)).IsRoot x := by
    filter_upwards [hev] with i hi
    apply IsAlgClosed.exists_root
    have hb : (p.natDegree : WithBot ℕ) ≤ (q.map (Pi.evalRingHom K i)).degree := by
      apply Polynomial.le_degree_of_ne_zero
      simpa using hi
    have hz : (0 : WithBot ℕ) < p.natDegree := by exact_mod_cast hn
    exact ne_of_gt (lt_of_lt_of_le hz hb)
  let r : ∀ i, K i := fun i => if h : ∃ x : K i,
      (q.map (Pi.evalRingHom K i)).IsRoot x then Classical.choose h else 0
  refine ⟨mk U K r, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply]
  apply (mk_eq_zero U K _).mpr
  filter_upwards [hroot] with i hi
  have hr : (q.map (Pi.evalRingHom K i)).eval (r i) = 0 := by
    dsimp only [r]
    rw [dite_eq_left hi]
    exact Classical.choose_spec hi
  rw [Polynomial.eval_map] at hr
  change (Pi.evalRingHom K i) (q.eval r) = 0
  rw [← Polynomial.eval₂_at_apply]
  exact hr

end UnitDistances.UltraField

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Loci
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.LocusAvoidance
open Polynomial Filter PowerGrowth
attribute [local instance] Classical.propDecidable
variable {K α ι : Type*} [Field K]

lemma zeros_subset (S : Finset α) (z w : α → K) (f : K[X][X]) : zeros S z w f ⊆ S :=
  Finset.filter_subset _ _

lemma zeros_one (S : Finset α) (z w : α → K) : zeros S z w 1=∅ := by
  simp [zeros]

lemma zeros_unit (S : Finset α) (z w : α → K) {f : K[X][X]} (hf : IsUnit f) :
    zeros S z w f=∅ := by
  obtain ⟨p,hp,rfl⟩ := Polynomial.isUnit_iff.mp hf
  obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hp
  have hc' : c ≠ 0 := hc.ne_zero
  simp [zeros,hc']

theorem exists_maximizer (S : Finset α) (z w : α → K) (D : ℕ) :
    ∃ f : K[X][X], f ≠ 0 ∧ BivariateDegree.size f ≤ D ∧
      ∀ g : K[X][X], g ≠ 0 → BivariateDegree.size g ≤ D →
        (zeros S z w g).card ≤ (zeros S z w f).card := by
  classical
  let A := S.powerset.filter fun T => ∃ f : K[X][X],
    f ≠ 0 ∧ BivariateDegree.size f ≤ D ∧ zeros S z w f=T
  have hA : A.Nonempty := by
    refine ⟨∅,Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.empty_subset _),?_⟩⟩
    refine ⟨1,one_ne_zero,?_,zeros_one S z w⟩
    simp [BivariateDegree.size]
  obtain ⟨T,hT,hmax⟩ := Finset.exists_max_image A Finset.card hA
  obtain ⟨f,hf,hd,rfl⟩ := (Finset.mem_filter.mp hT).2
  refine ⟨f,hf,hd,fun g hg hgd => hmax _ ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (zeros_subset S z w g),g,hg,hgd,rfl⟩

lemma size_X : BivariateDegree.size (X : K[X][X])=1 := by
  simp [BivariateDegree.size,Bivariate.swap_Y]

theorem exists_factor_witness (S : Finset α) (z w : α → K) (D : ℕ)
    (f : K[X][X]) (hf : f ≠ 0) (hd : BivariateDegree.size f ≤ D) :
    ∃ g : K[X][X], Irreducible g ∧ BivariateDegree.size g ≤ max D 1 ∧
      (¬IsUnit f → (zeros S z w f).card ≤ max D 1*(zeros S z w g).card) := by
  by_cases hnu : ¬IsUnit f
  · obtain ⟨g,hg,_,hdeg,hcount⟩ := BivariateDegree.irreducible_zero_capture S z w f hf hnu
    refine ⟨g,hg,hdeg.trans (hd.trans (le_max_left _ _)),fun _ => ?_⟩
    exact hcount.trans (Nat.mul_le_mul_right _ (hd.trans (le_max_left _ _)))
  · exact ⟨X,Polynomial.irreducible_X,by rw [size_X]; exact le_max_right _ _,fun h => False.elim (hnu h)⟩

theorem plane_or_curve (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (S : ι → Finset α) (z w : α → K) :
    (∀ D : ℕ, ∃ b : ℝ, 0<b ∧ ∀ᶠ i in U,∀ f : K[X][X],
      f ≠ 0 → BivariateDegree.size f ≤ D →
        ((zeros (S i) z w f).card : ℝ) ≤ t i^(1-b)) ∨
    ∃ D : ℕ,∃ f : ι → K[X][X],
      (∀ i,Irreducible (f i) ∧ BivariateDegree.size (f i) ≤ D) ∧
      Lower (U : Filter ι) t (fun i => ((zeros (S i) z w (f i)).card : ℝ)) 1 := by
  classical
  by_cases hplane : ∀ D : ℕ, ∃ b : ℝ, 0<b ∧ ∀ᶠ i in U,∀ f : K[X][X],
      f ≠ 0 → BivariateDegree.size f ≤ D →
        ((zeros (S i) z w f).card : ℝ) ≤ t i^(1-b)
  · exact Or.inl hplane
  · push Not at hplane
    obtain ⟨D,hD⟩ := hplane
    choose f hf hfd hfm using fun i => exists_maximizer (S i) z w D
    let m : ι → ℝ := fun i => (zeros (S i) z w (f i)).card
    have hm : Lower (U : Filter ι) t m 1 := by
      intro ε hε
      filter_upwards [hD ε hε] with i hi
      obtain ⟨g,hg,hgd,hgc⟩ := hi
      exact hgc.le.trans (Nat.cast_le.mpr (hfm i g hg hgd))
    have hnu : ∀ᶠ i in U,¬IsUnit (f i) := by
      filter_upwards [hm.eventually_pos ht] with i hi hunit
      have hz := zeros_unit (S i) z w hunit
      simp [m,hz] at hi
    choose g hg hgd hgc using fun i => exists_factor_witness (S i) z w D (f i) (hf i) (hfd i)
    have hM : 0<(max D 1 : ℕ) := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
    have hMr : 0<((max D 1 : ℕ) : ℝ) := Nat.cast_pos.mpr hM
    refine Or.inr ⟨max D 1,g,fun i => ⟨hg i,hgd i⟩,?_⟩
    apply (hm.const_mul ht (inv_pos.mpr hMr)).mono
    filter_upwards [hnu] with i hi
    have hc : m i ≤ ((max D 1 : ℕ) : ℝ)*(zeros (S i) z w (g i)).card := by
      dsimp only [m]
      exact_mod_cast hgc i hi
    rw [← div_eq_inv_mul]
    exact (div_le_iff₀ hMr).mpr (by simpa only [mul_comm] using hc)

end PlanarUnitDistances.LocusAvoidance

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_SmallHeight
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace UnitDistances.ExactHeightObstruction
open PlanarUnitDistances.WeightedAbsoluteValues
variable {K : Type*} [Field K] [NumberField K] [IsGalois ℚ K]
omit [IsGalois ℚ K] in
lemma height_root_le {m : ℕ} (hm : 0 < m) (a : Fin m → K) (x : K)
    (hx : x^m = ∑ i, a i*x^(i:ℕ)) :
    height x ≤ Real.log m + ∑ i, height (a i) := exactHeight_root_le K hm a x hx
end UnitDistances.ExactHeightObstruction

namespace UnitDistances.ExactSmallHeightField
open Filter Asymptotics
open scoped BigOperators
open ExactHeightObstruction UltraField

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)] (J : ι → ℝ)

variable {U K J}

omit [∀ i, IsGalois ℚ (K i)] in
theorem Negligible.congr {f g : ∀ i, K i} (hf : Negligible U K J f)
    (he : ∀ᶠ i in U, f i = g i) : Negligible U K J g := by
  apply hf.congr' _ (EventuallyEq.refl _ _)
  filter_upwards [he] with i hi
  rw [hi]

theorem mk_mem_constants_iff (hJ : Tendsto J U atTop) (f : ∀ i, K i) :
    mk U K f ∈ constants (K := K) hJ ↔ Negligible U K J f := by
  constructor
  · rintro ⟨g, he, hg⟩
    exact hg.congr ((mk_eq_mk U K _ _).mp he)
  · exact fun hf => ⟨f, rfl, hf⟩

omit [∀ i, IsGalois ℚ (K i)] in

theorem Negligible.root (hJ : Tendsto J U atTop) {m : ℕ} (hm : 0 < m)
    (a : Fin m → ∀ i, K i) (u : ∀ i, K i) (ha : ∀ j, Negligible U K J (a j))
    (hu : ∀ᶠ i in U, u i ^ m = ∑ j, a j i * u i ^ (j : ℕ)) :
    Negligible U K J u := by
  have hb : (fun i => height (u i)) =O[(U : Filter ι)]
      (fun i => Real.log m + ∑ j, height (a j i)) := by
    apply IsBigO.of_bound'
    filter_upwards [hu] with i hi
    rw [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _), Real.norm_eq_abs,
      abs_of_nonneg (add_nonneg (Real.log_nonneg (by exact_mod_cast hm))
        (Finset.sum_nonneg fun j _ => height_nonneg _))]
    exact height_root_le hm (fun j => a j i) (u i) hi
  apply hb.trans_isLittleO
  have hs := IsLittleO.sum (s := Finset.univ) (fun j _ => ha j)
  simpa only [Finset.sum_apply, Function.comp_def, id_eq] using
    ((isLittleO_const_id_atTop (Real.log m)).comp_tendsto hJ).add hs

theorem root_mem_constants (hJ : Tendsto J U atTop) {m : ℕ} (hm : 0 < m)
    (a : Fin m → constants (K := K) hJ) (u : FieldProduct U K)
    (hu : u ^ m = ∑ j, (a j : FieldProduct U K) * u ^ (j : ℕ)) :
    u ∈ constants (K := K) hJ := by
  classical
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective u
  choose b hb hsmall using fun j => (a j).property
  apply (mk_mem_constants_iff hJ f).mpr
  apply Negligible.root hJ hm b f hsmall
  have hrel : mk U K (f ^ m) = mk U K (∑ j, b j * f ^ (j : ℕ)) := by
    simpa only [map_pow, map_sum, map_mul, hb] using hu
  have he := (mk_eq_mk U K _ _).mp hrel
  simpa only [Pi.pow_apply, Finset.sum_apply, Pi.mul_apply] using he

theorem algebraic_mem_constants (hJ : Tendsto J U atTop) (u : FieldProduct U K)
    (hu : IsAlgebraic (constants (K := K) hJ) u) : u ∈ constants (K := K) hJ := by
  classical
  obtain ⟨p, hp, hz⟩ := hu.isIntegral
  have hm : 0 < p.natDegree :=
    Polynomial.natDegree_pos_of_aeval_root hp.ne_zero hz (fun x hx => by simpa using hx)
  apply root_mem_constants (K := K) hJ hm (fun j => -p.coeff (j : ℕ)) u
  change Polynomial.aeval u p = 0 at hz
  have hh := congrArg (Polynomial.aeval u) hp.as_sum
  rw [hz] at hh
  simp only [map_add, map_sum, map_mul, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C] at hh
  rw [← Fin.sum_univ_eq_sum_range] at hh
  simp only [Subfield.coe_neg, neg_mul, Finset.sum_neg_distrib]
  exact eq_neg_of_add_eq_zero_left hh.symm

theorem large_height_transcendental (hJ : Tendsto J U atTop) (f : ∀ i, K i)
    {c : ℝ} (hc : 0 < c) (hf : ∀ᶠ i in U, c * J i ≤ height (f i)) :
    Transcendental (constants (K := K) hJ) (mk U K f) := by
  intro halg
  have hsmall := (mk_mem_constants_iff hJ f).mp (algebraic_mem_constants hJ _ halg)
  have hbound := hsmall.bound (half_pos hc)
  obtain ⟨i, hi, hpos, hb⟩ := (hf.and ((hJ.eventually_gt_atTop 0).and hbound)).exists
  rw [Real.norm_eq_abs, abs_of_nonneg (height_nonneg _), Real.norm_eq_abs,
    abs_of_pos hpos] at hb
  have hh : 0 < c * J i := mul_pos hc hpos
  nlinarith

end UnitDistances.ExactSmallHeightField

namespace UnitDistances.UltraField
open Filter
variable {ι : Type*} (U : Ultrafilter ι) (K L : ι → Type*)
  [∀ i, Field (K i)] [∀ i, Field (L i)]

lemma transcendental_map {k : Type*} [Field k] [Algebra k (FieldProduct U K)]
    [Algebra k (FieldProduct U L)] (f : ∀ i, K i →+* L i)
    (hcomm : ∀ r : k, map U K L f (algebraMap k (FieldProduct U K) r)=
      algebraMap k (FieldProduct U L) r)
    (x : FieldProduct U K) (hx : Transcendental k x) :
    Transcendental k (map U K L f x) := by
  let φ : FieldProduct U K →ₐ[k] FieldProduct U L :=
    { map U K L f with commutes' := hcomm }
  intro h
  exact hx ((isAlgebraic_algHom_iff φ φ.injective).mp h)
end UnitDistances.UltraField

namespace PlanarUnitDistances.UltraHeightGrid
open Filter Asymptotics UnitDistances.UltraField UnitDistances.ExactSmallHeightField
open UnitDistances.ExactHeightObstruction
variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)]
  {J : ι → ℝ} (hJ : Tendsto J U atTop)

omit [∀ i, IsGalois ℚ (K i)] in
lemma negligible_of_bound (u : ∀ i,K i) (b : ι → ℝ) (hb : b=o[(U : Filter ι)] J)
    (hu : ∀ᶠ i in U,height (u i)≤b i) : Negligible U K J u := by
  have h : (fun i => height (u i))=O[(U : Filter ι)] b := by
    apply IsBigO.of_bound'
    filter_upwards [hu] with i hi
    rw [Real.norm_eq_abs,abs_of_nonneg (height_nonneg _),Real.norm_eq_abs]
    exact hi.trans (le_abs_self _)
  exact h.trans_isLittleO hb

variable (e : ∀ i,K i →+* ℂ)
variable [Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ))]
    (hcomm : ∀ r : constants (K := K) hJ,
      complexMap U K e r=algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r)

include hcomm
lemma large_transcendental (u : ∀ i,K i) {c : ℝ} (hc : 0<c)
    (hu : ∀ᶠ i in U,c*J i≤height (u i)) :
    Transcendental (constants (K := K) hJ)
      (mk U (fun _ => ℂ) (fun i => e i (u i))) :=
  transcendental_map U K (fun _ => ℂ) e hcomm (mk U K u)
    (large_height_transcendental hJ u hc hu)

lemma rectangle_constant (a b c d : ∀ i,K i)
    (hc : ∀ᶠ i in U,c i≠0) (hd : ∀ᶠ i in U,d i≠0)
    (hsmall : Negligible U K J (fun i => a i*b i/(c i*d i))) :
    ∃ r : constants (K := K) hJ,
      mk U (fun _ => ℂ) (fun i => e i (a i))*mk U (fun _ => ℂ) (fun i => e i (b i))=
      mk U (fun _ => ℂ) (fun i => e i (c i))*mk U (fun _ => ℂ) (fun i => e i (d i))*
        algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r := by
  let r : constants (K := K) hJ :=
    ⟨mk U K (fun i => a i*b i/(c i*d i)),(mk_mem_constants_iff hJ _).mpr hsmall⟩
  refine ⟨r,?_⟩
  rw [← hcomm r]
  change _=_*mk U (fun _ => ℂ) (fun i => e i (a i*b i/(c i*d i)))
  rw [← map_mul,← map_mul,← map_mul,mk_eq_mk]
  filter_upwards [hc,hd] with i hci hdi
  change e i (a i)*e i (b i)=e i (c i)*e i (d i)*e i (a i*b i/(c i*d i))
  simp only [map_div₀,map_mul]
  have hc' : e i (c i)≠0 := (map_ne_zero (e i)).mpr hci
  have hd' : e i (d i)≠0 := (map_ne_zero (e i)).mpr hdi
  field_simp [hc',hd']

end PlanarUnitDistances.UltraHeightGrid

namespace PlanarUnitDistances.EdgeLabels
open Filter Asymptotics UnitDistances.UltraField UnitDistances.ExactSmallHeightField
open UnitDistances.ExactHeightObstruction UltraHeightGrid
variable (U : Ultrafilter ℕ) (K : ℕ → Type)
  [∀ i, Field (K i)] [∀ i, NumberField (K i)] [∀ i, IsGalois ℚ (K i)]
  (J : ℕ → ℝ) (hJ : Tendsto J U atTop) (e : ∀ i,K i →+* ℂ)
variable [Algebra (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ))]
    (hcomm : ∀ r : constants (K := K) hJ,
      complexMap U K e r=algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) r)
variable (ell : ∀ n,ℂ → ℂ → K n)

include hJ hcomm in
lemma transcendental (p r : ℕ → ℂ) {c : ℝ} (hc : 0<c)
    (h : ∀ᶠ n in U,c*J n≤height (ell n (p n) (r n))) :
    Transcendental (constants (K := K) hJ) (label U K e ell p r) :=
  large_transcendental U K hJ e hcomm _ hc h

include hJ hcomm in
lemma rectangle (p p' r r' : ℕ → ℂ) (b : ℕ → ℝ) (hb : b=o[(U : Filter ℕ)] J)
    (hn : ∀ᶠ n in U,ell n (p n) (r' n)≠0 ∧ ell n (p' n) (r n)≠0)
    (h : ∀ᶠ n in U,height (ell n (p n) (r n)*ell n (p' n) (r' n)/
      (ell n (p n) (r' n)*ell n (p' n) (r n)))≤b n) :
    ∃ c : constants (K := K) hJ,
      label U K e ell p r*label U K e ell p' r'=
      label U K e ell p r'*label U K e ell p' r*
        algebraMap (constants (K := K) hJ) (FieldProduct U (fun _ => ℂ)) c := by
  exact rectangle_constant U K hJ e hcomm _ _ _ _
    (hn.mono fun _ hi => hi.1) (hn.mono fun _ hi => hi.2)
    (negligible_of_bound U K _ b hb h)

omit [∀ i, IsGalois ℚ (K i)] [∀ i, NumberField (K i)] in
lemma distance (p r : ℕ → ℂ)
    (h : ∀ᶠ n in U,(p n-r n)*(star (p n)-star (r n))=
      2-e n (ell n (p n) (r n))-(e n (ell n (p n) (r n)))⁻¹) :
    (mk U (fun _ => ℂ) p-mk U (fun _ => ℂ) r)*
      (mk U (fun _ => ℂ) (fun n => star (p n))-mk U (fun _ => ℂ) (fun n => star (r n)))=
      2-label U K e ell p r-(label U K e ell p r)⁻¹ := by
  unfold label
  rw [← map_sub,← map_sub,← map_mul,← mk_inv,← map_ofNat (mk U (fun _ => ℂ)) 2,
    ← map_sub,← map_sub,mk_eq_mk]
  exact h
end PlanarUnitDistances.EdgeLabels

namespace UnitDistances.GridCount
open scoped BigOperators
open Finset

lemma pow_expect_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (n : ℕ) :
    (𝔼 a, f a)^n ≤ 𝔼 a, (f a)^n := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := by positivity
  have h := (convexOn_pow (𝕜 := ℝ) n).map_sum_le
    (t := univ) (w := fun _ : α => (Fintype.card α : ℝ)⁻¹) (p := f)
    (by intros; positivity) (by simp [hc]) (by simpa using hf)
  simpa only [smul_eq_mul, ← Finset.mul_sum, Fintype.expect_eq_sum_div_card,
    div_eq_inv_mul] using h

lemma expect_prod_tuple {α : Type*} [Fintype α] (f : α → ℝ) (n : ℕ) :
    (𝔼 p : Fin n → α, ∏ i, f (p i)) = (𝔼 a, f a)^n := by
  classical
  simp only [Fintype.expect_eq_sum_div_card, ← Fintype.sum_pow,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, div_pow]

theorem complete_grid_density {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → ℝ) (hE : ∀ a b, 0 ≤ E a b)
    (N j : ℕ) :
    (𝔼 a, 𝔼 b, E a b)^(N*j) ≤
      𝔼 p : Fin N → α, 𝔼 r : Fin j → β, ∏ i, ∏ l, E (p i) (r l) := by
  classical
  let X : (Fin N → α) → ℝ := fun p => 𝔼 b, ∏ i, E (p i) b
  have hX : ∀ p, 0 ≤ X p := fun p =>
    Finset.expect_nonneg fun b _ => Finset.prod_nonneg fun i _ => hE (p i) b
  have hEX : (𝔼 a, 𝔼 b, E a b)^N ≤ 𝔼 p, X p := by
    calc
      (𝔼 a, 𝔼 b, E a b)^N = (𝔼 b, 𝔼 a, E a b)^N := by
        rw [Finset.expect_comm]
      _ ≤ 𝔼 b, (𝔼 a, E a b)^N := pow_expect_le _
        (fun b => Finset.expect_nonneg fun a _ => hE a b) N
      _ = 𝔼 b, 𝔼 p : Fin N → α, ∏ i, E (p i) b := by
        apply Finset.expect_congr rfl
        intro b _
        exact (expect_prod_tuple (fun a => E a b) N).symm
      _ = 𝔼 p, X p := by rw [Finset.expect_comm]
  calc
    (𝔼 a, 𝔼 b, E a b)^(N*j) = ((𝔼 a, 𝔼 b, E a b)^N)^j := (pow_mul _ _ _)
    _ ≤ (𝔼 p, X p)^j := pow_le_pow_left₀ (pow_nonneg (Finset.expect_nonneg fun a _ =>
      Finset.expect_nonneg fun b _ => hE a b) N) hEX j
    _ ≤ 𝔼 p, (X p)^j := pow_expect_le X hX j
    _ = 𝔼 p : Fin N → α, 𝔼 r : Fin j → β, ∏ i, ∏ l, E (p i) (r l) := by
      apply Finset.expect_congr rfl
      intro p _
      dsimp only [X]
      rw [← expect_prod_tuple]
      apply Finset.expect_congr rfl
      intro r _
      exact Finset.prod_comm

lemma expect_pair_indicator {α β : Type*} [Fintype α] [Fintype β]
    (E : α → β → Prop) [DecidableRel E] :
    (𝔼 a, 𝔼 b, if E a b then (1 : ℝ) else 0) =
      ((univ.filter fun ab : α × β => E ab.1 ab.2).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)) := by
  classical
  rw [← Finset.expect_product' univ univ]
  simp only [univ_product_univ, Fintype.expect_eq_sum_div_card,
    Finset.sum_boole, Fintype.card_prod, Nat.cast_mul]

theorem complete_grid_count {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (E : α → β → Prop) [DecidableRel E] (N j : ℕ) :
    (Fintype.card α : ℝ)^N * (Fintype.card β : ℝ)^j *
      (((univ.filter fun ab : α × β => E ab.1 ab.2).card : ℝ) /
        ((Fintype.card α : ℝ) * (Fintype.card β : ℝ)))^(N*j)
      ≤ (grids E N j).card := by
  classical
  have h := complete_grid_density (fun a b => if E a b then (1 : ℝ) else 0)
    (by intros; split_ifs <;> norm_num) N j
  simp only [Finset.prod_boole, mem_univ, forall_const] at h
  rw [expect_pair_indicator, expect_pair_indicator] at h
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  have hd : 0 < (Fintype.card α : ℝ)^N * (Fintype.card β : ℝ)^j := by positivity
  have hh := (le_div_iff₀ hd).mp h
  simpa only [grids, mul_comm] using hh

end UnitDistances.GridCount

namespace UnitDistances.GenericDiagonal
open Filter

theorem exists_avoiding {α τ : Type*} [DecidableEq α] (G : Finset α)
    (S : Finset τ) (bad : τ → Finset α)
    (h : ∑ s ∈ S, (bad s).card < G.card) :
    ∃ x ∈ G, ∀ s ∈ S, x ∉ bad s := by
  classical
  have hc : ¬G ⊆ S.biUnion bad := by
    intro hsub
    exact (not_le_of_gt h) ((Finset.card_le_card hsub).trans Finset.card_biUnion_le)
  obtain ⟨x, hx, hn⟩ := Finset.not_subset.mp hc
  exact ⟨x, hx, fun s hs hm => hn (Finset.mem_biUnion.mpr ⟨s, hs, hm⟩)⟩

theorem diagonal_nat {A : ℕ → Type*} [∀ n, Nonempty (A n)]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (good : ∀ n, A n → Prop) (test : ∀ n, ℕ → A n → Prop)
    (h : ∀ s, ∀ᶠ n in U, ∃ x, good n x ∧ ∀ a ≤ s, test n a x) :
    ∃ x : ∀ n, A n, (∀ᶠ n in U, good n (x n)) ∧
      ∀ a, ∀ᶠ n in U, test n a (x n) := by
  classical
  let P : ℕ → ℕ → Prop := fun n s => ∃ x, good n x ∧ ∀ a ≤ s, test n a x
  let s : ℕ → ℕ := fun n => Nat.findGreatest (P n) n
  let x : ∀ n, A n := fun n => if hn : P n (s n) then Classical.choose hn
    else Classical.choice (inferInstance : Nonempty (A n))
  have hprefix (a : ℕ) : ∀ᶠ n in U, P n (s n) ∧ a ≤ s n := by
    filter_upwards [h a, (eventually_ge_atTop a).filter_mono hU] with n hn hna
    exact ⟨Nat.findGreatest_spec hna hn, Nat.le_findGreatest hna hn⟩
  refine ⟨x, ?_, ?_⟩
  · filter_upwards [hprefix 0] with n hn
    dsimp only [x]
    rw [dite_eq_left hn.1]
    exact (Classical.choose_spec hn.1).1
  · intro a
    filter_upwards [hprefix a] with n hn
    dsimp only [x]
    rw [dite_eq_left hn.1]
    exact (Classical.choose_spec hn.1).2 a hn.2

theorem diagonal_countable {A : ℕ → Type*} [∀ n, Nonempty (A n)]
    {τ : Type*} [Countable τ] (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (good : ∀ n, A n → Prop) (test : ∀ n, τ → A n → Prop)
    (h : ∀ S : Finset τ, ∀ᶠ n in U, ∃ x, good n x ∧ ∀ a ∈ S, test n a x) :
    ∃ x : ∀ n, A n, (∀ᶠ n in U, good n (x n)) ∧
      ∀ a, ∀ᶠ n in U, test n a (x n) := by
  classical
  let := Encodable.ofCountable τ
  let tests : ℕ → Finset τ := fun s => (Finset.range (s+1)).biUnion
    (fun i => (Encodable.decode (α := τ) i).toFinset)
  have mem_tests (a : τ) : a ∈ tests (Encodable.encode a) := by
    apply Finset.mem_biUnion.mpr
    refine ⟨Encodable.encode a, Finset.mem_range.mpr (Nat.lt_succ_self _), ?_⟩
    simp
  obtain ⟨x, hx, htest⟩ := diagonal_nat U hU good
    (fun n s x => ∀ a ∈ tests s, test n a x) (by
      intro s
      filter_upwards [h (tests s)] with n hn
      obtain ⟨x, hx, hall⟩ := hn
      refine ⟨x, hx, fun a ha b hb => hall b ?_⟩
      apply Finset.biUnion_subset_biUnion_of_subset_left _ (Finset.range_mono (Nat.add_le_add_right ha 1)) hb)
  refine ⟨x, hx, fun a => ?_⟩
  filter_upwards [htest (Encodable.encode a)] with n hn
  exact hn a (mem_tests a)

end UnitDistances.GenericDiagonal

namespace PlanarUnitDistances.PowerGrowth
open Filter
variable {ι : Type*} {F : Filter ι} {t f g : ι → ℝ} {a b : ℝ}

lemma Lower.one (ht : Tendsto t F atTop) : Lower F t (fun _ => 1) 0 := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  simpa using Real.rpow_le_rpow_of_exponent_le hi (show 0 - ε ≤ 0 by linarith)

lemma Upper.one (ht : Tendsto t F atTop) : Upper F t (fun _ => 1) 0 := by
  intro ε hε
  filter_upwards [eventually_one_le ht] with i hi
  simpa using Real.one_le_rpow hi hε.le

lemma Lower.pow (hf : Lower F t f a) (ht : Tendsto t F atTop) (n : ℕ) :
    Lower F t (fun i => f i ^ n) (a * n) := by
  induction n with
  | zero => simpa using Lower.one ht
  | succ n ih =>
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using ih.mul hf ht

lemma Upper.pow (hf : Upper F t f a) (hn : ∀ᶠ i in F, 0 ≤ f i)
    (ht : Tendsto t F atTop) (n : ℕ) : Upper F t (fun i => f i ^ n) (a * n) := by
  induction n with
  | zero => simpa using Upper.one ht
  | succ n ih =>
    have hn' : ∀ᶠ i in F, 0 ≤ f i ^ n := hn.mono fun _ h => pow_nonneg h _
    simpa only [pow_succ, Nat.cast_add, Nat.cast_one, mul_add, mul_one] using ih.mul hf hn' hn ht

lemma eventually_lt_of_upper_lower (hf : Upper F t f a) (hg : Lower F t g b)
    (hab : a < b) (ht : Tendsto t F atTop) : ∀ᶠ i in F, f i < g i := by
  have hε : 0 < (b-a)/3 := by linarith
  filter_upwards [hf _ hε, hg _ hε, ht.eventually_gt_atTop 1] with i hi hj hti
  exact hi.trans_lt ((Real.rpow_lt_rpow_of_exponent_lt hti (by linarith)).trans_le hj)

lemma Saving.add (hf : Saving F t f a) (hg : Saving F t g a)
    (ht : Tendsto t F atTop) : Saving F t (fun i => f i + g i) a := by
  obtain ⟨b, hb, hf⟩ := hf
  obtain ⟨c, hc, hg⟩ := hg
  exact ⟨max b c, max_lt hb hc,
    (hf.exponent_mono (le_max_left _ _) ht).add (hg.exponent_mono (le_max_right _ _) ht) ht⟩

lemma Saving.zero (ht : Tendsto t F atTop) (a : ℝ) : Saving F t (fun _ => 0) a := by
  refine ⟨a-1, by linarith, ?_⟩
  intro ε _
  filter_upwards [eventually_base_pos ht] with i hi
  exact Real.rpow_nonneg hi.le _

lemma Saving.finset_sum {τ : Type*} (S : Finset τ) (f : τ → ι → ℝ)
    (hf : ∀ s ∈ S, Saving F t (f s) a) (ht : Tendsto t F atTop) :
    Saving F t (fun i => ∑ s ∈ S, f s i) a := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Saving.zero ht a
  | @insert s S hs ih =>
    simpa [Finset.sum_insert hs] using
      (hf s (Finset.mem_insert_self _ _)).add
        (ih fun x hx => hf x (Finset.mem_insert_of_mem hx)) ht

lemma Saving.eventually_lt (hf : Saving F t f a) (hg : Lower F t g a)
    (ht : Tendsto t F atTop) : ∀ᶠ i in F, f i < g i := by
  obtain ⟨b, hb, hf⟩ := hf
  exact eventually_lt_of_upper_lower hf hg hb ht
end PlanarUnitDistances.PowerGrowth

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Blocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GenericGrid
open Filter Finset PowerGrowth
open UnitDistances.GridCount UnitDistances.GenericDiagonal

variable {ι : Type*} {F : Filter ι} (t : ι → ℝ)
variable {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]

lemma edges_card_le (E : ∀ i, A i → B i → Prop) (i : ι) :
    ((edges E i).card : ℝ) ≤ (Fintype.card (A i) : ℝ) * Fintype.card (B i) := by
  classical
  have h : (edges E i).card ≤ Fintype.card (A i) * Fintype.card (B i) := by
    simpa [edges] using (Finset.card_filter_le (univ : Finset (A i × B i)) (fun ab => E i ab.1 ab.2))
  exact_mod_cast h

lemma side_card_lower (E : ∀ i, A i → B i → Prop) (ht : Tendsto t F atTop)
    (hA : Upper F t (fun i => Fintype.card (A i)) 1)
    (hB : Upper F t (fun i => Fintype.card (B i)) 1)
    (he : Lower F t (fun i => (edges E i).card) 2) :
    Lower F t (fun i => Fintype.card (A i)) 1 ∧
      Lower F t (fun i => Fintype.card (B i)) 1 := by
  have hpos : ∀ᶠ i in F, 0 < (Fintype.card (A i) : ℝ) ∧ 0 < (Fintype.card (B i) : ℝ) := by
    filter_upwards [he.eventually_pos ht] with i hi
    have hp := hi.trans_le (edges_card_le E i)
    constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card (A i)),
      Nat.cast_nonneg (α := ℝ) (Fintype.card (B i))]
  constructor
  · have hh := he.div hB (hpos.mono fun _ h => h.2) ht
    have hm : (fun i => ((edges E i).card : ℝ) / Fintype.card (B i)) ≤ᶠ[F]
        (fun i => (Fintype.card (A i) : ℝ)) := by
      filter_upwards [hpos] with i hi
      exact (div_le_iff₀ hi.2).mpr (edges_card_le E i)
    simpa only [show (2:ℝ)-1=1 by norm_num] using hh.mono hm
  · have hh := he.div hA (hpos.mono fun _ h => h.1) ht
    have hm : (fun i => ((edges E i).card : ℝ) / Fintype.card (A i)) ≤ᶠ[F]
        (fun i => (Fintype.card (B i) : ℝ)) := by
      filter_upwards [hpos] with i hi
      exact (div_le_iff₀ hi.1).mpr (by simpa [mul_comm] using edges_card_le E i)
    simpa only [show (2:ℝ)-1=1 by norm_num] using hh.mono hm

theorem grid_card_lower (E : ∀ i, A i → B i → Prop) (ht : Tendsto t F atTop)
    (hA : Upper F t (fun i => Fintype.card (A i)) 1)
    (hB : Upper F t (fun i => Fintype.card (B i)) 1)
    (he : Lower F t (fun i => (edges E i).card) 2) (N j : ℕ) :
    Lower F t (fun i => by classical exact ((grids (E i) N j).card : ℝ)) (N+j) := by
  classical
  obtain ⟨hA', hB'⟩ := side_card_lower t E ht hA hB he
  have hposA := hA'.eventually_pos ht
  have hposB := hB'.eventually_pos ht
  have hden := hA.mul hB (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hp : ∀ᶠ i in F, 0 < (Fintype.card (A i) : ℝ) * Fintype.card (B i) := by
    filter_upwards [hposA, hposB] with i ha hb
    exact mul_pos ha hb
  have hd := he.div hden hp ht
  have hcount := ((hA'.pow ht N).mul (hB'.pow ht j) ht).mul (hd.pow ht (N*j)) ht
  simp only [one_mul, show (2:ℝ)-(1+1)=0 by norm_num, zero_mul, add_zero] at hcount
  apply hcount.mono
  filter_upwards [hposA, hposB] with i ha hb
  have : Nonempty (A i) := Fintype.card_pos_iff.mp (by exact_mod_cast ha)
  have : Nonempty (B i) := Fintype.card_pos_iff.mp (by exact_mod_cast hb)
  exact complete_grid_count (E i) N j

theorem eventually_exists_avoiding {C : ι → Type*} [∀ i, DecidableEq (C i)]
    {τ : Type*} (G : ∀ i, Finset (C i)) (bad : ∀ i, τ → Finset (C i))
    {a : ℝ} (ht : Tendsto t F atTop)
    (hG : Lower F t (fun i => (G i).card) a)
    (hb : ∀ s, Saving F t (fun i => (bad i s).card) a) (S : Finset τ) :
    ∀ᶠ i in F, ∃ x ∈ G i, ∀ s ∈ S, x ∉ bad i s := by
  have hsum := Saving.finset_sum S (fun s i => ((bad i s).card : ℝ)) (fun s _ => hb s) ht
  have hlt := hsum.eventually_lt hG ht
  filter_upwards [hlt] with i hi
  apply exists_avoiding (G i) S (bad i)
  exact_mod_cast hi

theorem choose_countable {C : ℕ → Type*} [∀ i, Nonempty (C i)] [∀ i, DecidableEq (C i)]
    {τ : Type*} [Countable τ] (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (t : ℕ → ℝ) (G : ∀ i, Finset (C i)) (bad : ∀ i, τ → Finset (C i))
    {a : ℝ} (ht : Tendsto t (U : Filter ℕ) atTop)
    (hG : Lower (U : Filter ℕ) t (fun i => (G i).card) a)
    (hb : ∀ s, Saving (U : Filter ℕ) t (fun i => (bad i s).card) a) :
    ∃ x : ∀ i, C i, (∀ᶠ i in U, x i ∈ G i) ∧ ∀ s, ∀ᶠ i in U, x i ∉ bad i s := by
  exact diagonal_countable U hU (fun i x => x ∈ G i) (fun i s x => x ∉ bad i s)
    (fun S => eventually_exists_avoiding t G bad ht hG hb S)
end PlanarUnitDistances.GenericGrid

namespace UnitDistanceBlockAvoidance
open MvPolynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {F σ τ : Type*} [Field F]

lemma coeff_sumAlgEquiv (p : MvPolynomial (σ ⊕ τ) F)
    (a : σ →₀ ℕ) (b : τ →₀ ℕ) :
    ((sumAlgEquiv F σ τ p).coeff a).coeff b = p.coeff (a.sumElim b) := by
  simp only [sumAlgEquiv, AddMonoidAlgebra.curryAlgEquiv, AddMonoidAlgebra.curryRingEquiv,
    AddMonoidAlgebra.curryAddEquiv, MvPolynomial.coeff, AlgEquiv.trans_apply]
  simp [AddMonoidAlgebra.coeff_ofCoeff, AddMonoidAlgebra.coeff_domCongr, Finsupp.curry_apply,
    Finsupp.mapRange_apply, AddMonoidAlgebra.coeffAddEquiv]

lemma coeff_degree_le (p : MvPolynomial (σ ⊕ τ) F) (a : σ →₀ ℕ) :
    ((sumAlgEquiv F σ τ p).coeff a).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro b hb
  have h : a.sumElim b ∈ p.support := by
    rw [mem_support_iff] at hb ⊢
    rwa [← coeff_sumAlgEquiv]
  have hd := le_totalDegree h
  rw [Finsupp.sum_sumElim] at hd
  exact (Nat.le_add_left _ _).trans hd

lemma outer_degree_le (p : MvPolynomial (σ ⊕ τ) F) :
    (sumAlgEquiv F σ τ p).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree]
  apply Finset.sup_le
  intro a ha
  rw [mem_support_iff] at ha
  obtain ⟨b, hb⟩ : ∃ b, ((sumAlgEquiv F σ τ p).coeff a).coeff b ≠ 0 := by
    by_contra! h
    apply ha
    ext b
    simpa using h b
  have h : a.sumElim b ∈ p.support := by
    rwa [mem_support_iff, ← coeff_sumAlgEquiv]
  have hd := le_totalDegree h
  rw [Finsupp.sum_sumElim] at hd
  exact (Nat.le_add_right _ _).trans hd

lemma map_degree_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    (map f p).totalDegree ≤ p.totalDegree := by
  classical
  rw [totalDegree]
  exact Finset.sup_le fun a ha => le_totalDegree (support_map_subset f p ha)

lemma eval_blocks (p : MvPolynomial (σ ⊕ τ) F) (x : σ → F) (y : τ → F) :
    eval x (map (eval₂Hom (RingHom.id F) y) (sumAlgEquiv F σ τ p)) =
      eval (Sum.elim x y) p := by
  have h : ((aeval x).comp (mapAlgHom (aeval y))).comp
      (sumAlgEquiv F σ τ).toAlgHom = aeval (Sum.elim x y) := by
    ext i
    cases i <;> simp
  exact DFunLike.congr_fun h p

theorem two_block_zero_count {A B : Type*} [Fintype A] [Fintype B]
    (x : A → σ → F) (y : B → τ → F) (D a b : ℕ)
    (hx : ∀ q : MvPolynomial σ F, q ≠ 0 → q.totalDegree ≤ D →
      (Finset.univ.filter fun i => eval (x i) q = 0).card ≤ a)
    (hy : ∀ q : MvPolynomial τ F, q ≠ 0 → q.totalDegree ≤ D →
      (Finset.univ.filter fun j => eval (y j) q = 0).card ≤ b)
    (p : MvPolynomial (σ ⊕ τ) F) (hp : p ≠ 0) (hd : p.totalDegree ≤ D) :
    (Finset.univ.filter fun ij : A × B => eval (Sum.elim (x ij.1) (y ij.2)) p = 0).card
      ≤ a * Fintype.card B + Fintype.card A * b := by
  classical
  let P := sumAlgEquiv F σ τ p
  have hP : P ≠ 0 := by
    intro h
    apply hp
    exact (sumAlgEquiv F σ τ).injective (h.trans (map_zero _).symm)
  obtain ⟨m, hm⟩ : ∃ m, P.coeff m ≠ 0 := by
    by_contra! h
    apply hP
    apply MvPolynomial.ext
    intro m
    simpa only [MvPolynomial.coeff_zero] using h m
  let q := P.coeff m
  have hq : (Finset.univ.filter fun j => eval (y j) q = 0).card ≤ b :=
    hy q hm ((coeff_degree_le p m).trans hd)
  have hslice (j : B) :
      (Finset.univ.filter fun i => eval (Sum.elim (x i) (y j)) p = 0).card ≤
        a + if eval (y j) q = 0 then Fintype.card A else 0 := by
    by_cases hj : eval (y j) q = 0
    · simp only [hj, ↓reduceIte]
      exact (Finset.card_filter_le _ _).trans (Nat.le_add_left _ _)
    · simp only [hj, ↓reduceIte, add_zero]
      let r := map (eval₂Hom (RingHom.id F) (y j)) P
      have hr : r ≠ 0 := by
        intro hr
        apply hj
        have hc := congrArg (fun polynomial => polynomial.coeff m) hr
        simp only [r, coeff_map, MvPolynomial.coeff_zero] at hc
        exact hc
      have hrd : r.totalDegree ≤ D :=
        (map_degree_le _ P).trans ((outer_degree_le p).trans hd)
      simpa only [← eval_blocks, P, r] using hx r hr hrd
  calc
    _ = ∑ j : B, (Finset.univ.filter fun i =>
        eval (Sum.elim (x i) (y j)) p = 0).card := by
      simp only [Finset.card_filter, Fintype.sum_prod_type]
      exact Finset.sum_comm
    _ ≤ ∑ j : B, (a + if eval (y j) q = 0 then Fintype.card A else 0) :=
      Finset.sum_le_sum fun j _ => hslice j
    _ = a * Fintype.card B + Fintype.card A *
        (Finset.univ.filter fun j => eval (y j) q = 0).card := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, Finset.card_filter, Finset.mul_sum, mul_ite, mul_one, mul_zero]
      simp only [Nat.cast_id, mul_comm]
    _ ≤ _ := Nat.add_le_add_left (Nat.mul_le_mul_left _ hq) _

universe u

lemma blockTuples_card (A : Type*) [Fintype A] (n : ℕ) :
    Fintype.card (BlockTuples A n) = Fintype.card A ^ n := by
  induction n with
  | zero =>
    let : Unique (BlockTuples A 0) := inferInstanceAs (Unique PUnit)
    exact Fintype.card_unique
  | succ n ih =>
    change Fintype.card (BlockTuples A n × A) = _
    rw [Fintype.card_prod, ih, pow_succ]

lemma zeroCap_succ (m a n : ℕ) : zeroCap m a (n + 1) = (n + 1) * a * m ^ n := by
  induction n with
  | zero => simp [zeroCap]
  | succ n ih => rw [zeroCap, ih, pow_succ]; ring

theorem blocks_zero_count {A : Type*} [Fintype A]
    (x : A → σ → F) (D a : ℕ)
    (hx : ∀ q : MvPolynomial σ F, q ≠ 0 → q.totalDegree ≤ D →
      (Finset.univ.filter fun i => eval (x i) q = 0).card ≤ a)
    (n : ℕ) (p : MvPolynomial (BlockVars σ n) F)
    (hp : p ≠ 0) (hd : p.totalDegree ≤ D) :
    (Finset.univ.filter fun u => eval (blockEval x n u) p = 0).card ≤
      zeroCap (Fintype.card A) a n := by
  classical
  induction n with
  | zero =>
    let : IsEmpty (BlockVars σ 0) := inferInstanceAs (IsEmpty PEmpty)
    have hne (u : BlockTuples A 0) : eval (blockEval x 0 u) p ≠ 0 := by
      obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (BlockVars σ 0) p
      simpa only [eval_C, ne_eq, C_eq_zero] using hp
    have hz : (Finset.univ.filter fun u => eval (blockEval x 0 u) p = 0) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro u hu
      exact hne u (Finset.mem_filter.mp hu).2
    rw [hz]; exact Nat.zero_le _
  | succ n ih =>
    have h := two_block_zero_count (blockEval x n) x D
      (zeroCap (Fintype.card A) a n) a (fun q hq hqd => ih q hq hqd) hx p hp hd
    have he : (Finset.univ.filter fun u : BlockTuples A (n+1) =>
        eval (blockEval x (n+1) u) p = 0) =
        (Finset.univ.filter fun ij : BlockTuples A n × A =>
          eval (Sum.elim (blockEval x n ij.1) (x ij.2)) p = 0) := by
      apply Finset.ext
      intro u
      constructor <;> intro hu
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hu).2⟩
    rw [he]
    simpa only [zeroCap, blockTuples_card] using h

end UnitDistanceBlockAvoidance

namespace UnitDistanceBlockAvoidance
open MvPolynomial
open scoped BigOperators
variable {K A σ : Type*} [Field K] [Fintype A]

lemma attainable_zeros_nonempty (x : A → σ → K) (D : ℕ) :
    {m | ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = m}.Nonempty := by
  refine ⟨0, 1, one_ne_zero, ?_, ?_⟩
  · simp
  · simp [zeroSet]

lemma attainable_zeros_bdd (x : A → σ → K) (D : ℕ) :
    BddAbove {m | ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = m} := by
  refine ⟨Fintype.card A, ?_⟩
  rintro m ⟨p, _, _, rfl⟩
  classical
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

lemma zeroSet_card_le (x : A → σ → K) (D : ℕ) (p : MvPolynomial σ K)
    (hp : p ≠ 0) (hd : p.totalDegree ≤ D) : (zeroSet x p).card ≤ maxZeros x D :=
  le_csSup (attainable_zeros_bdd x D) ⟨p, hp, hd, rfl⟩

lemma maxZeros_attained (x : A → σ → K) (D : ℕ) :
    ∃ p : MvPolynomial σ K, p ≠ 0 ∧ p.totalDegree ≤ D ∧ (zeroSet x p).card = maxZeros x D :=
  Nat.sSup_mem (attainable_zeros_nonempty x D) (attainable_zeros_bdd x D)

lemma maxZeros_le (x : A → σ → K) (D : ℕ) (b : ℝ)
    (h : ∀ p : MvPolynomial σ K, p ≠ 0 → p.totalDegree ≤ D → ((zeroSet x p).card : ℝ) ≤ b) :
    (maxZeros x D : ℝ) ≤ b := by
  obtain ⟨p, hp, hd, he⟩ := maxZeros_attained x D
  simpa [he] using h p hp hd

lemma blockGrids_card {B : Type*} [Fintype B] (E : A → B → Prop) (N j : ℕ) :
    (blockGrids E N j).card = by classical exact (UnitDistances.GridCount.grids E N j).card := by
  classical
  exact Finset.card_map _

lemma mem_blockGrids {B : Type*} [Fintype B] (E : A → B → Prop) (N j : ℕ)
    (u : BlockTuples A N × BlockTuples B j) : u ∈ blockGrids E N j ↔
      ∀ i l, E (tupleEquiv A N u.1 i) (tupleEquiv B j u.2 l) := by
  classical
  simp [blockGrids, UnitDistances.GridCount.grids]
end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance
variable {ι : Type*} {F : Filter ι} {t : ι → ℝ}
variable {A B : ι → Type*} [∀ i, Fintype (A i)] [∀ i, Fintype (B i)]
variable {K σ τ : Type*} [Field K]

lemma zeroCap_upper (x : ∀ i, A i → σ → K) (D n : ℕ) {b : ℝ}
    (hcard : Upper F t (fun i => Fintype.card (A i)) 1)
    (hx : Upper F t (fun i => maxZeros (x i) D) b) (ht : Tendsto t F atTop) :
    Upper F t (fun i => (zeroCap (Fintype.card (A i)) (maxZeros (x i) D) (n+1) : ℝ))
      (b+n) := by
  have hm := hx.mul (hcard.pow (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht n)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => pow_nonneg (Nat.cast_nonneg _) _) ht
  have hh := hm.const_mul ht (show (0:ℝ) ≤ n+1 by positivity)
  simp only [one_mul] at hh
  apply hh.congr
  exact Eventually.of_forall fun i => by simp [zeroCap_succ, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, mul_assoc]

theorem polynomial_test_saving (x : ∀ i, A i → σ → K) (y : ∀ i, B i → τ → K)
    (hA : Upper F t (fun i => Fintype.card (A i)) 1)
    (hB : Upper F t (fun i => Fintype.card (B i)) 1)
    (hx : UniformBlocks F t x) (hy : UniformBlocks F t y) (ht : Tendsto t F atTop)
    (N j : ℕ)
    (p : ι → MvPolynomial (BlockVars σ (N+1) ⊕ BlockVars τ (j+1)) K)
    (D : ℕ) (hp : ∀ᶠ i in F, p i ≠ 0 ∧ (p i).totalDegree ≤ D) :
    Saving F t (fun i => (zeroSet (fun u : BlockTuples (A i) (N+1) × BlockTuples (B i) (j+1) =>
      Sum.elim (blockEval (x i) (N+1) u.1) (blockEval (y i) (j+1) u.2)) (p i)).card)
      ((N+1:ℕ)+(j+1:ℕ)) := by
  obtain ⟨b, hb, hx⟩ := hx D
  obtain ⟨c, hc, hy⟩ := hy D
  have hu := (zeroCap_upper x D N hA hx ht).mul
    (hB.pow (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht (j+1))
    (Eventually.of_forall fun _ => Nat.cast_nonneg _)
    (Eventually.of_forall fun _ => pow_nonneg (Nat.cast_nonneg _) _) ht
  have hv := (hA.pow (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht (N+1)).mul
    (zeroCap_upper y D j hB hy ht)
    (Eventually.of_forall fun _ => pow_nonneg (Nat.cast_nonneg _) _)
    (Eventually.of_forall fun _ => Nat.cast_nonneg _) ht
  have hs₁ : Saving F t
      (fun i => (zeroCap (Fintype.card (A i)) (maxZeros (x i) D) (N+1) : ℝ) *
        (Fintype.card (B i) : ℝ)^(j+1)) ((N+1:ℕ)+(j+1:ℕ)) := by
    refine ⟨_, ?_, hu⟩
    push_cast
    linarith
  have hs₂ : Saving F t
      (fun i => (Fintype.card (A i) : ℝ)^(N+1) *
        (zeroCap (Fintype.card (B i)) (maxZeros (y i) D) (j+1) : ℝ))
      ((N+1:ℕ)+(j+1:ℕ)) := by
    refine ⟨_, ?_, hv⟩
    push_cast
    linarith
  obtain ⟨e, he, hh⟩ := hs₁.add hs₂ ht
  refine ⟨e, he, hh.mono ?_⟩
  filter_upwards [hp] with i hi
  have h := two_block_zero_count (blockEval (x i) (N+1)) (blockEval (y i) (j+1)) D
    (zeroCap (Fintype.card (A i)) (maxZeros (x i) D) (N+1))
    (zeroCap (Fintype.card (B i)) (maxZeros (y i) D) (j+1))
    (fun q hq hd => blocks_zero_count (x i) D (maxZeros (x i) D)
      (fun r hr hrd => zeroSet_card_le (x i) D r hr hrd) (N+1) q hq hd)
    (fun q hq hd => blocks_zero_count (y i) D (maxZeros (y i) D)
      (fun r hr hrd => zeroSet_card_le (y i) D r hr hrd) (j+1) q hq hd)
    (p i) hi.1 hi.2
  have haCard : Fintype.card (BlockTuples (A i) (N+1)) = Fintype.card (A i) ^ (N+1) :=
    (Fintype.card_congr (tupleEquiv (A i) (N+1))).trans (by simp)
  have hbCard : Fintype.card (BlockTuples (B i) (j+1)) = Fintype.card (B i) ^ (j+1) :=
    (Fintype.card_congr (tupleEquiv (B i) (j+1))).trans (by simp)
  rw [haCard, hbCard] at h
  exact_mod_cast h
end PlanarUnitDistances.GenericGrid

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance
variable {K σ τ : Type*} [Field K]
variable {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]

theorem choose_polynomial_tests {T : Type*} [Countable T]
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (t : ℕ → ℝ)
    (ht : Tendsto t (U : Filter ℕ) atTop)
    (E : ∀ n, A n → B n → Prop)
    (hA : Upper (U : Filter ℕ) t (fun n => Fintype.card (A n)) 1)
    (hB : Upper (U : Filter ℕ) t (fun n => Fintype.card (B n)) 1)
    (he : Lower (U : Filter ℕ) t (fun n => (edges E n).card) 2)
    (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K)
    (hx : UniformBlocks (U : Filter ℕ) t x) (hy : UniformBlocks (U : Filter ℕ) t y)
    (N j : ℕ) (p : T → ℕ → MvPolynomial (BlockVars σ (N+1) ⊕ BlockVars τ (j+1)) K)
    (hp : ∀ s, ∃ D : ℕ, ∀ᶠ n in U, p s n ≠ 0 ∧ (p s n).totalDegree ≤ D) :
    ∃ u : ∀ n, Option (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)),
      (∀ᶠ n in U, ∃ v, u n = some v ∧ v ∈ blockGrids (E n) (N+1) (j+1)) ∧
      ∀ s, ∀ᶠ n in U, eval (optionalCoordinates x y (N+1) (j+1) n (u n)) (p s n) ≠ 0 := by
  classical
  let emb (n : ℕ) : (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)) ↪
      Option (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)) :=
    ⟨some, Option.some_injective _⟩
  let G n := (blockGrids (E n) (N+1) (j+1)).map (emb n)
  let bad n s := (zeroSet (fun v : BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1) =>
      Sum.elim (blockEval (x n) (N+1) v.1) (blockEval (y n) (j+1) v.2)) (p s n)).map (emb n)
  have hG : Lower (U : Filter ℕ) t (fun n => (G n).card) ((N+1:ℕ)+(j+1:ℕ)) := by
    apply (grid_card_lower t E ht hA hB he (N+1) (j+1)).congr
    exact Eventually.of_forall fun n => by
      simp only [G, Finset.card_map]
      exact_mod_cast (blockGrids_card (E n) (N+1) (j+1)).symm
  have hb : ∀ s, Saving (U : Filter ℕ) t (fun n => (bad n s).card) ((N+1:ℕ)+(j+1:ℕ)) := by
    intro s
    obtain ⟨D, hD⟩ := hp s
    obtain ⟨e, he, h⟩ := polynomial_test_saving x y hA hB hx hy ht N j (p s) D hD
    refine ⟨e, he, h.congr ?_⟩
    exact Eventually.of_forall fun n => by simp [bad]
  obtain ⟨u, hu, hs⟩ := choose_countable U hU t G bad ht hG hb
  have hgood : ∀ᶠ n in U, ∃ v, u n = some v ∧ v ∈ blockGrids (E n) (N+1) (j+1) := by
    filter_upwards [hu] with n hn
    obtain ⟨v, hv, hvu⟩ := Finset.mem_map.mp hn
    exact ⟨v, hvu.symm, hv⟩
  refine ⟨u, hgood, ?_⟩
  intro s
  filter_upwards [hgood, hs s] with n hn hns
  obtain ⟨v, hvu, hv⟩ := hn
  rw [hvu]
  intro hzero
  apply hns
  apply Finset.mem_map.mpr
  refine ⟨v, ?_, hvu.symm⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzero⟩
end PlanarUnitDistances.GenericGrid

namespace UnitDistances.UltraField
open Filter MvPolynomial
variable {ι σ : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i, Field (K i)]

lemma mvmap_zero_iff (p : MvPolynomial σ (∀ i, K i)) :
    MvPolynomial.map (mk U K) p = 0 ↔
      ∀ᶠ i in U, MvPolynomial.map (Pi.evalRingHom K i) p = 0 := by
  classical
  constructor
  · intro hz
    have hc (m : σ →₀ ℕ) : ∀ᶠ i in U, p.coeff m i = 0 := by
      apply (mk_eq_zero U K _).mp
      simpa only [coeff_map, MvPolynomial.coeff_zero]
        using congrArg (fun polynomial => polynomial.coeff m) hz
    filter_upwards [(eventually_all_finset p.support).mpr (fun m _ => hc m)] with i hi
    ext m
    rw [coeff_map, MvPolynomial.coeff_zero]
    by_cases hm : m ∈ p.support
    · exact hi m hm
    · rw [notMem_support_iff.mp hm]
      rfl
  · intro hz
    ext m
    rw [coeff_map, MvPolynomial.coeff_zero, mk_eq_zero]
    filter_upwards [hz] with i hi
    simpa only [coeff_map, MvPolynomial.coeff_zero, Pi.evalRingHom_apply]
      using congrArg (fun polynomial => polynomial.coeff m) hi

lemma mvmap_eventually_ne_zero (p : MvPolynomial σ (∀ i, K i))
    (hp : MvPolynomial.map (mk U K) p ≠ 0) :
    ∀ᶠ i in U, MvPolynomial.map (Pi.evalRingHom K i) p ≠ 0 :=
  Ultrafilter.eventually_not.mpr ((mvmap_zero_iff U K p).not.mp hp)

lemma mvmap_totalDegree_le {R S : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* S) (p : MvPolynomial σ R) :
    (MvPolynomial.map φ p).totalDegree ≤ p.totalDegree := by
  classical
  apply Finset.sup_mono
  exact MvPolynomial.support_map_subset _ _

lemma mvmap_eval (p : MvPolynomial σ (∀ i, K i)) (x : σ → ∀ i, K i) :
    eval (fun s => mk U K (x s)) (MvPolynomial.map (mk U K) p) =
      mk U K (fun i => eval (fun s => x s i) (MvPolynomial.map (Pi.evalRingHom K i) p)) := by
  rw [eval_map]
  change eval₂ (mk U K) ((mk U K) ∘ x) p = _
  rw [← MvPolynomial.eval₂_comp]
  congr 1
  funext i
  symm
  rw [eval_map]
  exact MvPolynomial.eval₂_comp (Pi.evalRingHom K i) x p |>.symm
end UnitDistances.UltraField

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth MvPolynomial UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {K σ τ : Type*} [Field K] [Countable σ] [Countable τ]
variable {A B : ℕ → Type*} [∀ n, Fintype (A n)] [∀ n, Fintype (B n)]

theorem exists_independent_grid
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) (t : ℕ → ℝ)
    (ht : Tendsto t (U : Filter ℕ) atTop)
    (E : ∀ n, A n → B n → Prop)
    (hA : Upper (U : Filter ℕ) t (fun n => Fintype.card (A n)) 1)
    (hB : Upper (U : Filter ℕ) t (fun n => Fintype.card (B n)) 1)
    (he : Lower (U : Filter ℕ) t (fun n => (edges E n).card) 2)
    (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K)
    (hx : UniformBlocks (U : Filter ℕ) t x) (hy : UniformBlocks (U : Filter ℕ) t y)
    (N j : ℕ) (L : Type*) [Field L] [Countable L]
    [Algebra L (FieldProduct U (fun _ => K))] :
    ∃ u : ∀ n, Option (BlockTuples (A n) (N+1) × BlockTuples (B n) (j+1)),
      (∀ᶠ n in U, ∃ v, u n = some v ∧ v ∈ blockGrids (E n) (N+1) (j+1)) ∧
      AlgebraicIndependent L (fun s => mk U (fun _ => K)
        (fun n => optionalCoordinates x y (N+1) (j+1) n (u n) s)) := by
  classical
  let V := BlockVars σ (N+1) ⊕ BlockVars τ (j+1)
  have : Countable (MvPolynomial V L) :=
    AddMonoidAlgebra.coeff_injective.countable
  let T := {p : MvPolynomial V L // p ≠ 0}
  let φ := algebraMap L (FieldProduct U (fun _ => K))
  have lift (p : T) : ∃ q : MvPolynomial V (ℕ → K),
      MvPolynomial.map (mk U (fun _ => K)) q = MvPolynomial.map φ p.val :=
    MvPolynomial.map_surjective _ Ideal.Quotient.mk_surjective _
  choose q hq using lift
  let tests (s : T) (n : ℕ) := MvPolynomial.map (Pi.evalRingHom (fun _ => K) n) (q s)
  have hp (s : T) : ∃ D, ∀ᶠ n in U, tests s n ≠ 0 ∧ (tests s n).totalDegree ≤ D := by
    refine ⟨(q s).totalDegree, ?_⟩
    have hn : MvPolynomial.map (mk U (fun _ => K)) (q s) ≠ 0 := by
      rw [hq s]
      simpa only [map_zero] using (MvPolynomial.map_injective φ φ.injective).ne s.property
    filter_upwards [mvmap_eventually_ne_zero U (fun _ => K) (q s) hn] with n hn
    exact ⟨hn, mvmap_totalDegree_le _ _⟩
  obtain ⟨u, hu, htst⟩ := choose_polynomial_tests U hU t ht E hA hB he x y hx hy N j tests hp
  refine ⟨u, hu, algebraicIndependent_iff.mpr ?_⟩
  intro p hzero
  by_contra hp0
  let s : T := ⟨p, hp0⟩
  have heval : eval (fun v => mk U (fun _ => K)
        (fun n => optionalCoordinates x y (N+1) (j+1) n (u n) v))
      (MvPolynomial.map (mk U (fun _ => K)) (q s)) = 0 := by
    rw [hq s, eval_map]
    exact hzero
  rw [mvmap_eval] at heval
  have hz := (mk_eq_zero U (fun _ => K) _).mp heval
  have hn := htst s
  obtain ⟨n, hn0, hn1⟩ := (hz.and hn).exists
  exact hn1 hn0
end PlanarUnitDistances.GenericGrid

namespace UnitDistanceBlockAvoidance
variable {A σ F : Type*}

lemma varIndex_injective (σ : Type*) (n : ℕ) : Function.Injective (varIndex σ n) := by
  induction n with
  | zero => intro i; exact Fin.elim0 i.1
  | succ n ih =>
    rintro ⟨i,s⟩ ⟨j,t⟩ h
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact Prod.ext rfl (Sum.inr.inj h)
      | succ j => simp [varIndex] at h
    | succ i =>
      induction j using Fin.cases with
      | zero => simp [varIndex] at h
      | succ j =>
        have hh : (i,s)=(j,t) := ih (Sum.inl.inj h)
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj hh
        rfl

lemma blockEval_varIndex (x : A → σ → F) (n : ℕ) (u : BlockTuples A n)
    (ij : Fin n × σ) :
    blockEval x n u (varIndex σ n ij)=x (tupleEquiv A n u ij.1) ij.2 := by
  induction n with
  | zero => exact Fin.elim0 ij.1
  | succ n ih =>
    obtain ⟨j,s⟩ := ij
    induction j using Fin.cases with
    | zero => rfl
    | succ j =>
      exact ih u.1 (j,s)
end UnitDistanceBlockAvoidance

namespace PlanarUnitDistances.GenericGrid
open Filter UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {K σ τ L : Type*} [Field K] [Field L]
variable {A B : ℕ → Type*}

lemma independent_left_right (U : Ultrafilter ℕ)
    [Algebra L (FieldProduct U (fun _ => K))]
    (x : ∀ n, A n → σ → K) (y : ∀ n, B n → τ → K) (N j : ℕ)
    (u : ∀ n, Option (BlockTuples (A n) N × BlockTuples (B n) j))
    (h : AlgebraicIndependent L (fun s => mk U (fun _ => K)
      (fun n => optionalCoordinates x y N j n (u n) s))) :
    AlgebraicIndependent L (fun is => mk U (fun _ => K) (fun n => leftCoords x N j n (u n) is)) ∧
    AlgebraicIndependent L (fun is => mk U (fun _ => K) (fun n => rightCoords y N j n (u n) is)) := by
  constructor
  · convert h.comp (fun is => Sum.inl (varIndex σ N is))
      (Sum.inl_injective.comp (varIndex_injective σ N)) using 1
    funext is
    congr 1
    funext n
    cases hu : u n with
    | none => rfl
    | some v => exact (blockEval_varIndex (x n) N v.1 is).symm
  · convert h.comp (fun is => Sum.inr (varIndex τ j is))
      (Sum.inr_injective.comp (varIndex_injective τ j)) using 1
    funext is
    congr 1
    funext n
    cases hu : u n with
    | none => rfl
    | some v => exact (blockEval_varIndex (y n) j v.2 is).symm
end PlanarUnitDistances.GenericGrid

namespace PlanarUnitDistances.GenericGrid
open Filter PowerGrowth UnitDistanceBlockAvoidance UnitDistances.UltraField
variable {σ τ : Type*} [Countable σ] [Countable τ]

theorem exists_real_grid (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (t : ℕ → ℝ) (ht : Tendsto t (U : Filter ℕ) atTop)
    (A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
    (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
    (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
    (he : Lower (U : Filter ℕ) t
      (fun n => (edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
    (x : ℂ → σ → ℂ) (y : ℂ → τ → ℂ)
    (hx0 : ∀ s, x 0 s=0) (hy0 : ∀ s, y 0 s=0)
    (hx : UniformBlocks (U : Filter ℕ) t (fun n (a : A n) => x a))
    (hy : UniformBlocks (U : Filter ℕ) t (fun n (b : B n) => y b))
    (N j : ℕ) (L : Type*) [Field L] [Countable L]
    [Algebra L (FieldProduct U (fun _ => ℂ))] :
    ∃ p : Fin (N+1) → ℕ → ℂ, ∃ r : Fin (j+1) → ℕ → ℂ,
      (∀ᶠ n in U, ∀ i j, p i n ∈ A n ∧ r j n ∈ B n ∧ E n (p i n) (r j n)) ∧
      AlgebraicIndependent L (fun iq : Fin (N+1) × σ => mk U (fun _ => ℂ)
        (fun n => x (p iq.1 n) iq.2)) ∧
      AlgebraicIndependent L (fun iq : Fin (j+1) × τ => mk U (fun _ => ℂ)
        (fun n => y (r iq.1 n) iq.2)) := by
  classical
  obtain ⟨u,hu,hai⟩ := exists_independent_grid U hU t ht
    (fun n (a : A n) (b : B n) => E n a b)
    (by simpa only [Fintype.card_coe] using hA)
    (by simpa only [Fintype.card_coe] using hB) he
    (fun n (a : A n) => x a) (fun n (b : B n) => y b) hx hy N j L
  let p : Fin (N+1) → ℕ → ℂ := fun i n => match u n with
    | none => 0
    | some v => (tupleEquiv (A n) (N+1) v.1 i).val
  let r : Fin (j+1) → ℕ → ℂ := fun i n => match u n with
    | none => 0
    | some v => (tupleEquiv (B n) (j+1) v.2 i).val
  refine ⟨p,r,?_,?_,?_⟩
  · filter_upwards [hu] with n hn
    obtain ⟨v,hv,he⟩ := hn
    intro i q
    refine ⟨?_,?_,?_⟩
    · simpa only [p,hv] using (tupleEquiv (A n) (N+1) v.1 i).property
    · simpa only [r,hv] using (tupleEquiv (B n) (j+1) v.2 q).property
    · simpa only [p,r,hv] using (mem_blockGrids _ _ _ v).mp he i q
  · have hh := (independent_left_right U _ _ _ _ u hai).1
    convert hh using 1
    funext iq
    congr 1
    funext n
    cases hv : u n with
    | none => simpa only [p,hv,leftCoords] using hx0 iq.2
    | some v => simp only [p,hv,leftCoords]
  · have hh := (independent_left_right U _ _ _ _ u hai).2
    convert hh using 1
    funext iq
    congr 1
    funext n
    cases hv : u n with
    | none => simpa only [r,hv,rightCoords] using hy0 iq.2
    | some v => simp only [r,hv,rightCoords]
end PlanarUnitDistances.GenericGrid

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_Obstruction
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.PolynomialBlocks
open MvPolynomial
open scoped BigOperators

lemma natDegree_eval₂_le {R S σ : Type*} [CommSemiring R] [CommSemiring S]
    (φ : R →+* Polynomial S) (x : σ → Polynomial S)
    (hφ : ∀ r, (φ r).natDegree = 0) (hx : ∀ i, (x i).natDegree ≤ 1)
    (p : MvPolynomial σ R) : (eval₂ φ x p).natDegree ≤ p.totalDegree := by
  classical
  rw [MvPolynomial.eval₂_eq]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  apply Polynomial.natDegree_mul_le.trans
  rw [hφ, zero_add]
  apply (Polynomial.natDegree_prod_le _ _).trans
  apply le_trans (Finset.sum_le_sum fun i _ =>
    Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left (d i) (hx i)))
  simpa only [mul_one, Finsupp.sum] using (MvPolynomial.le_totalDegree hd)

lemma unique_natDegree_le {R σ : Type*} [CommSemiring R] [Unique σ]
    (p : MvPolynomial σ R) : (uniqueAlgEquiv R σ p).natDegree ≤ p.totalDegree := by
  rw [uniqueAlgEquiv_apply]
  exact natDegree_eval₂_le Polynomial.C (fun _ => Polynomial.X)
    (fun _ => Polynomial.natDegree_C _) (fun _ => Polynomial.natDegree_X_le) p

lemma unique_eval {R σ : Type*} [CommSemiring R] [Unique σ]
    (p : MvPolynomial σ R) (z : R) :
    Polynomial.eval z (uniqueAlgEquiv R σ p) = eval (fun _ => z) p := by
  rw [uniqueAlgEquiv_apply]
  have h := MvPolynomial.eval₂_comp_left (Polynomial.evalRingHom z) Polynomial.C
    (fun _ : σ => Polynomial.X) p
  have hφ : (Polynomial.evalRingHom z).comp Polynomial.C = RingHom.id R := by ext; simp
  have hx : (Polynomial.evalRingHom z) ∘ (fun _ : σ => Polynomial.X) = fun _ => z := by
    funext i
    simp
  rw [hφ, hx] at h
  exact h

lemma bivar_eval {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) (z w : K) :
    (bivar p).eval₂ (Polynomial.evalRingHom z) w = eval ![z,w] p := by
  have h : (Polynomial.eval₂RingHom (Polynomial.evalRingHom z) w).comp
      (Polynomial.Bivariate.equivMvPolynomial K).symm.toRingHom = MvPolynomial.eval ![z,w] := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp
    · intro i
      fin_cases i <;> simp
  exact DFunLike.congr_fun h p

lemma bivar_natDegree_le {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :
    (bivar p).natDegree ≤ p.totalDegree := by
  change (MvPolynomial.eval₂ (algebraMap K (Polynomial (Polynomial K)))
    ![Polynomial.C Polynomial.X, Polynomial.X] p).natDegree ≤ _
  apply natDegree_eval₂_le
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

lemma swap_bivar {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :
    Polynomial.Bivariate.swap (bivar p) =
      MvPolynomial.eval₂ (algebraMap K (Polynomial (Polynomial K)))
        ![Polynomial.X, Polynomial.C Polynomial.X] p := by
  have h : Polynomial.Bivariate.swap.toAlgHom.comp
      (Polynomial.Bivariate.equivMvPolynomial K).symm.toAlgHom =
      (MvPolynomial.aeval ![Polynomial.X, Polynomial.C Polynomial.X] :
        MvPolynomial (Fin 2) K →ₐ[K] Polynomial (Polynomial K)) := by
    ext i
    fin_cases i <;> simp [Polynomial.Bivariate.swap]
  exact DFunLike.congr_fun h p

lemma swap_bivar_natDegree_le {K : Type*} [Field K] (p : MvPolynomial (Fin 2) K) :
    (Polynomial.Bivariate.swap (bivar p)).natDegree ≤ p.totalDegree := by
  rw [swap_bivar]
  apply natDegree_eval₂_le
  · intro r
    simp
  · intro i
    fin_cases i <;> simp

lemma unique_zeros_card_le {K A σ : Type*} [Field K] [Fintype A] [Unique σ]
    (z : A → K) (hz : Function.Injective z) (p : MvPolynomial σ K) (hp : p ≠ 0) :
    (by classical exact (Finset.univ.filter fun a => eval (fun _ => z a) p = 0).card) ≤
      p.totalDegree := by
  classical
  let S := Finset.univ.filter fun a => eval (fun _ => z a) p = 0
  let q := uniqueAlgEquiv K σ p
  have hq : q ≠ 0 := by
    simpa only [map_zero] using (uniqueAlgEquiv K σ).injective.ne hp
  have h : (S.image z).card ≤ q.natDegree := by
    apply Polynomial.card_le_degree_of_subset_roots
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    apply (Polynomial.mem_roots hq).mpr
    exact (unique_eval p (z i)).trans (Finset.mem_filter.mp hi).2
  rw [Finset.card_image_of_injective _ hz] at h
  exact h.trans (unique_natDegree_le p)
end PlanarUnitDistances.PolynomialBlocks

namespace PlanarUnitDistances.FiniteGraphPruning
open Finset
attribute [local instance] Classical.propDecidable

lemma mass_nonneg {α β : Type*} (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) : 0 ≤ mass w P Q :=
  Finset.sum_nonneg (fun p hp => Finset.sum_nonneg (hw p hp))

theorem prune {α β : Type*} (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) (he : 0 < mass w P Q) :
    ∃ A ⊆ P,∃ B ⊆ Q,
      mass w P Q/2 ≤ mass w A B ∧
      (∀ p ∈ A,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ q ∈ B,w p q) ∧
      (∀ q ∈ B,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ p ∈ A,w p q) := by
  classical
  have hP : P.Nonempty := by
    by_contra h
    have hz : P=∅ := Finset.not_nonempty_iff_eq_empty.mp h
    simp [mass,hz] at he
  have hv : 0<(P.card : ℝ)+Q.card := by
    have hh : (0 : ℝ)<P.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hP)
    positivity
  let d := mass w P Q/(2*((P.card : ℝ)+Q.card))
  have hd : 0 ≤ d := div_nonneg (mass_nonneg w P Q hw) (by positivity)
  let potential (A : Finset α) (B : Finset β) := mass w A B-d*((A.card : ℝ)+B.card)
  obtain ⟨⟨A,B⟩,hAB,hmax⟩ := Finset.exists_max_image (P.powerset ×ˢ Q.powerset)
    (fun AB => potential AB.1 AB.2)
    (by exact ⟨(P,Q),by simp⟩)
  have hA : A ⊆ P := Finset.mem_powerset.mp (Finset.mem_product.mp hAB).1
  have hB : B ⊆ Q := Finset.mem_powerset.mp (Finset.mem_product.mp hAB).2
  have hfull := hmax (P,Q) (by simp)
  have hhalf : potential P Q=mass w P Q/2 := by
    dsimp [potential,d]
    field_simp [ne_of_gt hv]
    ring
  rw [hhalf] at hfull
  refine ⟨A,hA,B,hB,?_,?_,?_⟩
  · exact hfull.trans (sub_le_self _ (mul_nonneg hd (by positivity)))
  · intro p hp
    have hcomp := hmax (A.erase p,B) (by
      simp only [Finset.mem_product,Finset.mem_powerset]
      exact ⟨(Finset.erase_subset p A).trans hA,hB⟩)
    have hm : mass w (A.erase p) B+(∑ q ∈ B,w p q)=mass w A B :=
      Finset.sum_erase_add _ _ hp
    have hc : ((A.erase p).card : ℝ)+1=(A.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hp
    change mass w (A.erase p) B-d*(((A.erase p).card : ℝ)+B.card) ≤
      mass w A B-d*((A.card : ℝ)+B.card) at hcomp
    change d ≤ _
    nlinarith
  · intro q hq
    have hcomp := hmax (A,B.erase q) (by
      simp only [Finset.mem_product,Finset.mem_powerset]
      exact ⟨hA,(Finset.erase_subset q B).trans hB⟩)
    have hm : mass w A (B.erase q)+(∑ p ∈ A,w p q)=mass w A B := by
      unfold mass
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun p _ => Finset.sum_erase_add _ _ hq)
    have hc : ((B.erase q).card : ℝ)+1=(B.card : ℝ) := by
      exact_mod_cast Finset.card_erase_add_one hq
    change mass w A (B.erase q)-d*((A.card : ℝ)+(B.erase q).card) ≤
      mass w A B-d*((A.card : ℝ)+B.card) at hcomp
    change d ≤ _
    nlinarith

end PlanarUnitDistances.FiniteGraphPruning

namespace PlanarUnitDistances.DenseLoci
open Filter PowerGrowth FiniteGraphPruning LocusAvoidance Polynomial
attribute [local instance] Classical.propDecidable
variable {α β ι : Type*}

lemma mass_swap (w : α → β → ℝ) (P : Finset α) (Q : Finset β) :
    mass (fun q p => w p q) Q P=mass w P Q := by
  exact Finset.sum_comm

lemma mass_le_card_mul (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,w p q ≤ 1) : mass w P Q ≤ (P.card : ℝ)*Q.card := by
  calc
    mass w P Q ≤ ∑ p ∈ P,∑ q ∈ Q,(1 : ℝ) :=
      Finset.sum_le_sum (fun p hp => Finset.sum_le_sum (hw p hp))
    _ = _ := by simp

lemma cards_pos_of_mass_pos (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (h : 0 < mass w P Q) : 0<(P.card : ℝ) ∧ 0<(Q.card : ℝ) := by
  have hp : P.Nonempty := by
    by_contra hh
    simp [Finset.not_nonempty_iff_eq_empty.mp hh,mass] at h
  have hq : Q.Nonempty := by
    by_contra hh
    simp [Finset.not_nonempty_iff_eq_empty.mp hh,mass] at h
  exact ⟨Nat.cast_pos.mpr (Finset.card_pos.mpr hp),Nat.cast_pos.mpr (Finset.card_pos.mpr hq)⟩

lemma prune_nonneg (w : α → β → ℝ) (P : Finset α) (Q : Finset β)
    (hw : ∀ p ∈ P,∀ q ∈ Q,0 ≤ w p q) :
    ∃ A ⊆ P,∃ B ⊆ Q,
      mass w P Q/2 ≤ mass w A B ∧
      (∀ p ∈ A,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ q ∈ B,w p q) ∧
      (∀ q ∈ B,mass w P Q/(2*((P.card : ℝ)+Q.card)) ≤ ∑ p ∈ A,w p q) := by
  by_cases he : 0 < mass w P Q
  · exact prune w P Q hw he
  · have hz : mass w P Q=0 := le_antisymm (le_of_not_gt he) (mass_nonneg w P Q hw)
    refine ⟨P,Finset.Subset.refl _,Q,Finset.Subset.refl _,?_,?_,?_⟩
    · simp only [hz,zero_div,le_refl]
    · intro p hp
      simpa only [hz,zero_div] using Finset.sum_nonneg (hw p hp)
    · intro q hq
      simpa only [hz,zero_div] using Finset.sum_nonneg (fun p hp => hw p hp q hq)

lemma mass_restrict_lower (w : α → β → ℝ) (P A : Finset α) (Q : Finset β)
    (hA : A ⊆ P) (d : ℝ) (hd : ∀ p ∈ P,d ≤ ∑ q ∈ Q,w p q) :
    (A.card : ℝ)*d ≤ mass w A Q := by
  calc
    (A.card : ℝ)*d = ∑ _p ∈ A,d := by simp
    _ ≤ mass w A Q := Finset.sum_le_sum (fun p hp => hd p (hA hp))

theorem sequence_prune (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (hw : ∀ i,∀ p ∈ P i,∀ q ∈ Q i,0 ≤ w i p q)
    (hP : Upper (U : Filter ι) t (fun i => (P i).card) 1)
    (hQ : Upper (U : Filter ι) t (fun i => (Q i).card) 1)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    ∃ A : ι → Finset α,∃ B : ι → Finset β,∃ d : ι → ℝ,
      (∀ i,A i ⊆ P i ∧ B i ⊆ Q i) ∧
      Lower (U : Filter ι) t (fun i => mass (w i) (A i) (B i)) 2 ∧
      Lower (U : Filter ι) t d 1 ∧
      (∀ i,∀ p ∈ A i,d i ≤ ∑ q ∈ B i,w i p q) ∧
      (∀ i,∀ q ∈ B i,d i ≤ ∑ p ∈ A i,w i p q) := by
  classical
  choose A hA B hB hmass hleft hright using fun i => prune_nonneg (w i) (P i) (Q i) (hw i)
  let d := fun i => mass (w i) (P i) (Q i)/(2*((P i).card+(Q i).card : ℝ))
  have hed : Lower (U : Filter ι) t (fun i => mass (w i) (A i) (B i)) 2 := by
    apply (he.const_mul ht (show (0:ℝ)<1/2 by norm_num)).mono
    exact Eventually.of_forall fun i => by simpa only [one_div,div_eq_inv_mul,mul_one] using hmass i
  have huv : Upper (U : Filter ι) t (fun i => 2*((P i).card+(Q i).card : ℝ)) 1 :=
    (hP.add hQ ht).const_mul ht (by norm_num)
  have hpos : ∀ᶠ i in U,0<2*((P i).card+(Q i).card : ℝ) := by
    filter_upwards [he.eventually_pos ht] with i hi
    have hpp := cards_pos_of_mass_pos (w i) (P i) (Q i) hi
    exact mul_pos (by norm_num) (add_pos hpp.1 hpp.2)
  have hd : Lower (U : Filter ι) t d 1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using he.div huv hpos ht
  exact ⟨A,B,d,fun i => ⟨hA i,hB i⟩,hed,hd,hleft,hright⟩

lemma upper_card_subset (U : Ultrafilter ι) (t : ι → ℝ)
    {A P : ι → Finset α} (hP : Upper (U : Filter ι) t (fun i => (P i).card) 1)
    (hA : ∀ i,A i ⊆ P i) : Upper (U : Filter ι) t (fun i => (A i).card) 1 :=
  hP.mono (Eventually.of_forall fun i => Nat.cast_le.mpr (Finset.card_le_card (hA i)))

lemma lower_card_of_dense (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (hw : ∀ i,∀ p ∈ P i,∀ q ∈ Q i,w i p q ≤ 1)
    (hQ : Upper (U : Filter ι) t (fun i => (Q i).card) 1)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    Lower (U : Filter ι) t (fun i => (P i).card) 1 := by
  have hpos : ∀ᶠ i in U,0<((Q i).card : ℝ) := by
    filter_upwards [he.eventually_pos ht] with i hi
    exact (cards_pos_of_mass_pos (w i) (P i) (Q i) hi).2
  have hh := he.div hQ hpos ht
  have hmono : (fun i => mass (w i) (P i) (Q i)/((Q i).card : ℝ)) ≤ᶠ[U]
      (fun i => ((P i).card : ℝ)) := by
    filter_upwards [hpos] with i hi
    exact (div_le_iff₀ hi).mpr (mass_le_card_mul (w i) (P i) (Q i) (hw i))
  simpa only [show (2:ℝ)-1=1 by norm_num] using hh.mono hmono

variable {K : Type*} [Field K]

lemma Controlled.mono {U : Ultrafilter ι} {t : ι → ℝ} {P A : ι → Finset α} {z v : α → K}
    (h : Controlled U t P z v) (hA : ∀ i,A i ⊆ P i) : Controlled U t A z v := by
  rcases h with h|⟨D,f,hf,hcover⟩
  · left
    intro D
    obtain ⟨b,hb,hbound⟩ := h D
    refine ⟨b,hb,?_⟩
    filter_upwards [hbound] with i hi g hg hgd
    apply (Nat.cast_le.mpr (Finset.card_le_card ?_)).trans (hi g hg hgd)
    exact Finset.filter_subset_filter _ (hA i)
  · right
    refine ⟨D,f,hf,?_⟩
    filter_upwards [hcover] with i hi p hp
    exact hi p (hA i hp)

theorem control_left (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (z v : α → K) (d : ι → ℝ)
    (hd : Lower (U : Filter ι) t d 1)
    (hdeg : ∀ i,∀ p ∈ P i,d i ≤ ∑ q ∈ Q i,w i p q)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    ∃ A : ι → Finset α,(∀ i,A i ⊆ P i) ∧ Controlled U t A z v ∧
      Lower (U : Filter ι) t (fun i => mass (w i) (A i) (Q i)) 2 := by
  classical
  rcases plane_or_curve U t ht P z v with h|⟨D,f,hf,hfull⟩
  · exact ⟨P,fun _ => Finset.Subset.refl _,Or.inl h,he⟩
  · let A := fun i => zeros (P i) z v (f i)
    have hA : ∀ i,A i ⊆ P i := fun i => zeros_subset _ _ _ _
    refine ⟨A,hA,Or.inr ⟨D,f,hf,Eventually.of_forall fun i p hp => (Finset.mem_filter.mp hp).2⟩,?_⟩
    have hh := hfull.mul hd ht
    have hmono : (fun i => ((A i).card : ℝ)*d i) ≤ᶠ[U]
        (fun i => mass (w i) (A i) (Q i)) := Eventually.of_forall fun i =>
      mass_restrict_lower (w i) (P i) (A i) (Q i) (hA i) (d i) (hdeg i)
    simpa only [show (1:ℝ)+1=2 by norm_num] using hh.mono hmono

theorem controlled_subsets (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (Q : ι → Finset β)
    (w : ι → α → β → ℝ) (z₁ v₁ : α → K) (z₂ v₂ : β → K)
    (hw : ∀ i,∀ p ∈ P i,∀ q ∈ Q i,0 ≤ w i p q)
    (hP : Upper (U : Filter ι) t (fun i => (P i).card) 1)
    (hQ : Upper (U : Filter ι) t (fun i => (Q i).card) 1)
    (he : Lower (U : Filter ι) t (fun i => mass (w i) (P i) (Q i)) 2) :
    ∃ A : ι → Finset α,∃ B : ι → Finset β,∃ d : ι → ℝ,
      (∀ i,A i ⊆ P i ∧ B i ⊆ Q i) ∧
      Lower (U : Filter ι) t (fun i => mass (w i) (A i) (B i)) 2 ∧
      Lower (U : Filter ι) t d 1 ∧
      (∀ i,∀ p ∈ A i,d i ≤ ∑ q ∈ B i,w i p q) ∧
      (∀ i,∀ q ∈ B i,d i ≤ ∑ p ∈ A i,w i p q) ∧
      Controlled U t A z₁ v₁ ∧ Controlled U t B z₂ v₂ := by
  obtain ⟨P₀,Q₀,d₀,hsub₀,he₀,hd₀,hleft₀,_⟩ := sequence_prune U t ht P Q w hw hP hQ he
  obtain ⟨P₁,hP₁,hC₁,he₁⟩ := control_left U t ht P₀ Q₀ w z₁ v₁ d₀ hd₀ hleft₀ he₀
  have hP₁P : ∀ i,P₁ i ⊆ P i := fun i => (hP₁ i).trans (hsub₀ i).1
  have hQ₀Q : ∀ i,Q₀ i ⊆ Q i := fun i => (hsub₀ i).2
  have hw₁ : ∀ i,∀ p ∈ P₁ i,∀ q ∈ Q₀ i,0 ≤ w i p q :=
    fun i p hp q hq => hw i p (hP₁P i hp) q (hQ₀Q i hq)
  obtain ⟨P₂,Q₂,d₂,hsub₂,he₂,hd₂,_,hright₂⟩ := sequence_prune U t ht P₁ Q₀ w hw₁
    (upper_card_subset U t hP hP₁P) (upper_card_subset U t hQ hQ₀Q) he₁
  have he₂' : Lower (U : Filter ι) t
      (fun i => mass (fun q p => w i p q) (Q₂ i) (P₂ i)) 2 :=
    he₂.congr (Eventually.of_forall fun i => (mass_swap (w i) (P₂ i) (Q₂ i)).symm)
  obtain ⟨Q₃,hQ₃,hC₃,he₃'⟩ := control_left U t ht Q₂ P₂ (fun i q p => w i p q)
    z₂ v₂ d₂ hd₂ hright₂ he₂'
  have he₃ : Lower (U : Filter ι) t (fun i => mass (w i) (P₂ i) (Q₃ i)) 2 :=
    he₃'.congr (Eventually.of_forall fun i => mass_swap (w i) (P₂ i) (Q₃ i))
  have hP₂P : ∀ i,P₂ i ⊆ P i := fun i => (hsub₂ i).1.trans (hP₁P i)
  have hQ₃Q : ∀ i,Q₃ i ⊆ Q i := fun i => (hQ₃ i).trans ((hsub₂ i).2.trans (hQ₀Q i))
  have hw₃ : ∀ i,∀ p ∈ P₂ i,∀ q ∈ Q₃ i,0 ≤ w i p q :=
    fun i p hp q hq => hw i p (hP₂P i hp) q (hQ₃Q i hq)
  obtain ⟨A,B,d,hsub,he',hd,hleft,hright⟩ := sequence_prune U t ht P₂ Q₃ w hw₃
    (upper_card_subset U t hP hP₂P) (upper_card_subset U t hQ hQ₃Q) he₃
  refine ⟨A,B,d,fun i => ⟨(hsub i).1.trans (hP₂P i),(hsub i).2.trans (hQ₃Q i)⟩,
    he',hd,hleft,hright,?_,?_⟩
  · exact hC₁.mono (fun i => (hsub i).1.trans (hsub₂ i).1)
  · exact hC₃.mono (fun i => (hsub i).2)

end PlanarUnitDistances.DenseLoci

namespace PlanarUnitDistances.LocusBlocks
open Filter PowerGrowth GenericGrid PolynomialBlocks UnitDistanceBlockAvoidance MvPolynomial
variable {ι α K : Type*} [Field K]

lemma plane_zeros_card (P : Finset α) (z w : α → K) (p : MvPolynomial (Fin 2) K) :
    (zeroSet (fun a : P => ![z a,w a]) p).card =
      (LocusAvoidance.zeros P z w (bivar p)).card := by
  classical
  apply Finset.card_bij (fun (a : P) _ => (a : α))
  · intro a ha
    exact Finset.mem_filter.mpr ⟨a.property, by
      simpa only [bivar_eval] using (Finset.mem_filter.mp ha).2⟩
  · intro a _ b _ h
    exact Subtype.ext h
  · intro a ha
    refine ⟨⟨a,(Finset.mem_filter.mp ha).1⟩, ?_, rfl⟩
    simp only [zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
    simpa only [bivar_eval] using (Finset.mem_filter.mp ha).2

theorem plane_uniformBlocks (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (P : ι → Finset α) (z w : α → K)
    (h : DenseLoci.Uniform U t P z w) :
    UniformBlocks (U : Filter ι) t (fun i (a : P i) => ![z a,w a]) := by
  intro D
  obtain ⟨b,hb,hh⟩ := h (2*D)
  refine ⟨1-b, by linarith, ?_⟩
  intro ε hε
  filter_upwards [hh, eventually_one_le ht] with i hi hti
  apply (maxZeros_le _ D (t i ^ (1-b)) ?_).trans
    (Real.rpow_le_rpow_of_exponent_le hti (by linarith))
  intro p hp hpd
  rw [plane_zeros_card]
  apply hi (bivar p)
  · exact fun hz => hp ((Polynomial.Bivariate.equivMvPolynomial K).symm.injective
        (hz.trans (map_zero _).symm))
  · unfold BivariateDegree.size
    exact (Nat.add_le_add (bivar_natDegree_le p) (swap_bivar_natDegree_le p)).trans
      (by omega)

theorem curve_uniformBlocks {A : ι → Type*} [∀ i, Fintype (A i)]
    {σ : Type*} [Unique σ] (F : Filter ι) (t : ι → ℝ)
    (ht : Tendsto t F atTop) (z : ∀ i, A i → K) (hz : ∀ i, Function.Injective (z i)) :
    UniformBlocks F t (fun i a (_ : σ) => z i a) := by
  intro D
  refine ⟨0, by norm_num, ?_⟩
  intro ε hε
  filter_upwards [eventually_constant_le_rpow ht hε (D:ℝ)] with i hi
  apply (maxZeros_le _ D (D:ℝ) ?_).trans
  · simpa only [zero_add] using hi
  · intro p hp hd
    exact_mod_cast (unique_zeros_card_le (z i) (hz i) p hp).trans hd
end PlanarUnitDistances.LocusBlocks

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Asymptotics Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth FiniteGraphPruning BivariateMaps

lemma mass_indicator (P Q : Finset ℂ) (E : ℂ → ℂ → Prop) :
    mass (indicator E) P Q =
      (GenericGrid.edges (fun (_ : Unit) (a : P) (b : Q) => E a b) ()).card := by
  classical
  simp only [mass,indicator,GenericGrid.edges]
  rw [Finset.card_filter]
  simp only [Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  rw [← Finset.univ_product_univ,Finset.sum_product]
  rw [Finset.sum_subtype P (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_subtype Q (fun _ => Iff.rfl) _

lemma single_independent {B : Type} [Field B] (U : Ultrafilter ℕ)
    [Algebra B (UltraCurve.CU U)] {m : ℕ} (p : Fin m → ℕ → ℂ)
    (h : AlgebraicIndependent B (fun iq : Fin m × Fin 1 => z U (p iq.1))) :
    AlgebraicIndependent B (fun i => z U (p i)) :=
  h.comp (fun i => (i,0)) (fun _ _ he => congrArg Prod.fst he)

variable (U : Ultrafilter ℕ) (t J : ℕ → ℝ) (P : ℕ → Finset ℂ)
  (E : ℕ → ℂ → ℂ → Prop) (K : ℕ → Type)
  [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)

variable {U t J P E K e ell}
lemma grid_labels (hJ : Tendsto J U atTop)
    [Algebra (constants (K := K) hJ) (UltraCurve.CU U)]
    (hcomm : ∀ r : constants (K := K) hJ,
      UltraHeightGrid.complexMap U K e r=algebraMap (constants (K := K) hJ) (UltraCurve.CU U) r)
    (H : Hypotheses U t J P E K e ell) (p : Fin 21 → ℕ → ℂ) (r : Fin 4 → ℕ → ℂ)
    (hgrid : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n)) :
    let l := fun i j => EdgeLabels.label U K e ell (p i) (r j)
    (∀ i j,Transcendental (constants (K := K) hJ) (l i j)) ∧
    (∀ i j,∃ c : constants (K := K) hJ,
      l i j*l 0 0=l i 0*l 0 j*algebraMap (constants (K := K) hJ) (UltraCurve.CU U) c) ∧
    (∀ i j,(z U (p i)-z U (r j))*(w U (p i)-w U (r j))=2-l i j-(l i j)⁻¹) := by
  obtain ⟨c,hc,hlarge⟩ := H.large
  obtain ⟨b,hb,hsmall⟩ := H.rectangle
  refine ⟨?_,?_,?_⟩
  · intro i j
    apply EdgeLabels.transcendental U K J hJ e hcomm ell (p i) (r j) hc
    filter_upwards [hgrid] with n hn
    exact hlarge n _ (hn i j).1 _ (hn i j).2.1 (hn i j).2.2
  · intro i j
    apply EdgeLabels.rectangle U K J hJ e hcomm ell (p i) (p 0) (r j) (r 0) b hb
    · filter_upwards [hgrid] with n hn
      exact ⟨H.nonzero n _ (hn i 0).1 _ (hn i 0).2.1 (hn i 0).2.2,
        H.nonzero n _ (hn 0 j).1 _ (hn 0 j).2.1 (hn 0 j).2.2⟩
    · filter_upwards [hgrid] with n hn
      exact hsmall n _ (hn i j).1 _ (hn 0 j).1 _ (hn i j).2.1 _ (hn i 0).2.1
        (hn i j).2.2 (hn i 0).2.2 (hn 0 j).2.2 (hn 0 0).2.2
  · intro i j
    apply EdgeLabels.distance U K e ell (p i) (r j)
    filter_upwards [hgrid] with n hn
    exact H.distance n _ (hn i j).1 _ (hn i j).2.1 (hn i j).2.2
end PlanarUnitDistances.AlgebraicObstruction

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter Polynomial UnitDistances.UltraField
open UnitDistances.ExactSmallHeightField UnitDistances.ExactHeightObstruction
open PowerGrowth BivariateMaps
variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop) (t J : ℕ → ℝ)
  (ht : Tendsto t (U : Filter ℕ) atTop) (hJ : Tendsto J (U : Filter ℕ) atTop)
  (P A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
  (hsub : ∀ n,A n⊆P n ∧ B n⊆P n)
  (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
  (he : Lower (U : Filter ℕ) t
    (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
  (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
  (H : Hypotheses U t J P E K e ell)

include hU ht hJ hsub hA hB he H
lemma plane (hplane : DenseLoci.Uniform U t A id star) : False := by
  let : Algebra (constants (K := K) hJ) (UltraCurve.CU U) :=
    UltraHeightGrid.complexAlgebra U K hJ e
  obtain ⟨p,r,hgrid,hp,hr⟩ := GenericGrid.exists_real_grid U hU t ht A B E hA hB he
    (fun p : ℂ => ![p,star p]) (fun p : ℂ => fun _ : Fin 1 => p)
    (by intro s; fin_cases s <;> simp) (by intro s; rfl)
    (LocusBlocks.plane_uniformBlocks U t ht A id star hplane)
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (b : B n) => (b:ℂ))
      (fun _ => Subtype.val_injective)) 20 3 ℚ
  have hg : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n) := by
    filter_upwards [hgrid] with n hn i j
    exact ⟨(hsub n).1 (hn i j).1,(hsub n).2 (hn i j).2.1,(hn i j).2.2⟩
  obtain ⟨htrans,hrect,hdist⟩ := grid_labels hJ (fun _ => rfl) H p r hg
  let x : Fin 21 × Fin 2 → UltraCurve.CU U := fun iq => ![z U (p iq.1),w U (p iq.1)] iq.2
  have hx : AlgebraicIndependent ℚ x := by
    convert hp using 1
    all_goals try with_reducible_and_instances rfl
    funext ⟨i,j⟩
    fin_cases j <;> rfl
  have hr' : AlgebraicIndependent ℚ (fun j => z U (r j)) := single_independent U r hr
  apply GridObstruction.plane x hx (fun j => z U (r j)) (fun j => w U (r j))
    (fun i j hh => hr'.injective (congrArg Prod.fst hh))
    (fun i j => EdgeLabels.label U K e ell (p i) (r j)) htrans hrect
  intro i j
  exact hdist i j
end PlanarUnitDistances.AlgebraicObstruction

namespace PlanarUnitDistances.AlgebraicObstruction
open Filter UnitDistances.UltraField PowerGrowth FiniteGraphPruning

theorem no_rectangles_oai (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop)
    (t J : ℕ → ℝ) (ht : Tendsto t (U : Filter ℕ) atTop)
    (hJ : Tendsto J (U : Filter ℕ) atTop) (P : ℕ → Finset ℂ)
    (hP : Upper (U : Filter ℕ) t (fun n => (P n).card) 1)
    (E : ℕ → ℂ → ℂ → Prop)
    (he : Lower (U : Filter ℕ) t
      (fun n => (GenericGrid.edges (fun n (a : P n) (b : P n) => E n a b) n).card) 2)
    (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
    (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
    (H : Hypotheses U t J P E K e ell) : False := by
  classical
  have heP : Lower (U : Filter ℕ) t
      (fun n => mass (indicator (E n)) (P n) (P n)) 2 :=
    he.congr (Eventually.of_forall fun n => (mass_indicator (P n) (P n) (E n)).symm)
  have hn n p r : 0 ≤ indicator (E n) p r := by unfold indicator; split_ifs <;> norm_num
  have hl n p r : indicator (E n) p r ≤ 1 := by unfold indicator; split_ifs <;> norm_num
  obtain ⟨A,B,d,hsub,heAB,hd,hlA,hlB,hca,hcb⟩ := DenseLoci.controlled_subsets U t ht
    P P (fun n => indicator (E n)) id star id star (fun n p _ r _ => hn n p r) hP hP heP
  have hA := DenseLoci.upper_card_subset U t hP (fun n => (hsub n).1)
  have hB := DenseLoci.upper_card_subset U t hP (fun n => (hsub n).2)
  have hAf := DenseLoci.lower_card_of_dense U t ht A B (fun n => indicator (E n))
    (fun n p _ r _ => hl n p r) hB heAB
  have hBf := DenseLoci.lower_card_of_dense U t ht B A (fun n r p => indicator (E n) p r)
    (fun n r _ p _ => hl n p r) hA
    (heAB.congr (Eventually.of_forall fun n => by unfold mass; exact Finset.sum_comm.symm))
  have heG : Lower (U : Filter ℕ) t
      (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2 :=
    heAB.congr (Eventually.of_forall fun n => mass_indicator (A n) (B n) (E n))
  rcases hca with hplane|hcurve
  · exact plane U hU t J ht hJ P A B E hsub hA hB heG K e ell H hplane
  · rcases hcb with hplane|hcurveB
    · exact curve_plane U hU t J ht hJ P A B E hsub hA hB hAf heG K e ell H hcurve hplane
    · exact curve_curve U hU t J ht hJ P A B E hsub hA hB hAf hBf heG K e ell H hcurve hcurveB
end PlanarUnitDistances.AlgebraicObstruction

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.AlgebraicObstruction.no_rectangles_oai := @OAI.PlanarUnitDistances.AlgebraicObstruction.no_rectangles_oai
