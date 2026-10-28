-- Prove2me | solution 1 for OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T02:57:33.940043+00:00
-- url     : https://prove2.me/submissions/1beb6bb5-379c-45f2-b5ee-ff0c41f290e2

import Mathlib
import Definitions.Def_PlanarUnitDistances
import Definitions.Def_OAIQ2Un000

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

lemma Lower.tendsto_atTop (hf : Lower F t f a) (ht : Tendsto t F atTop) (ha : 0<a) :
    Tendsto f F atTop := by
  have he : 0<a-a/2 := by linarith
  exact tendsto_atTop_mono' F (hf (a/2) (by positivity))
    ((_root_.tendsto_rpow_atTop he).comp ht)

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

end Plane

section GenericLine

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable {ι : Type*} {a : ι → K}

lemma independent_difference_ne (ha : AlgebraicIndependent B a)
    {i j : ι} (hij : i ≠ j) (c : B) :
    a i - a j ≠ algebraMap B K c := by
  classical
  intro he
  have hp : (MvPolynomial.X i - MvPolynomial.X j : MvPolynomial ι B) =
      MvPolynomial.C c := ha (by simpa using he)
  have h0 := congrArg (MvPolynomial.eval (fun _ : ι => (0 : B))) hp
  have h1 := congrArg (MvPolynomial.eval (fun k : ι => if k = i then (1 : B) else 0)) hp
  simp only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C, sub_self] at h0
  simp [hij.symm] at h1
  exact one_ne_zero (h1.trans h0.symm)

variable [CharZero B] [CharZero K]

lemma line_root_simple (e c a : K) (h : e * c ^ 2 = 4) :
    (lineRadicandPoly e a).eval (a + c) = 0 ∧
    (lineRadicandPoly e a).derivative.eval (a + c) ≠ 0 := by
  have he : e ≠ 0 := by intro he; simp [he] at h
  have hc : c ≠ 0 := by intro hc; simp [hc] at h
  have hL : (lineDistancePoly e a).eval (a + c) = 4 := by
    simpa [lineDistancePoly] using h
  have hL' : (lineDistancePoly e a).derivative.eval (a + c) = 2 * e * c := by
    simp [lineDistancePoly, derivative_mul, derivative_pow]
    ring
  constructor
  · simp [lineRadicandPoly, hL]
  · simpa [lineRadicandPoly, derivative_mul, derivative_sub, hL, hL'] using
      mul_ne_zero (by norm_num : (8 : K) ≠ 0) (mul_ne_zero he hc)

lemma line_root_other (ha : AlgebraicIndependent B a) (e c : B)
    (hec : e * c ^ 2 = 4) {i j : ι} (hji : j ≠ i) :
    (lineRadicandPoly (algebraMap B K e) (a j)).eval
      (a i + algebraMap B K c) ≠ 0 := by
  have he : e ≠ 0 := by intro he; simp [he] at hec
  have he' : algebraMap B K e ≠ 0 := (map_ne_zero (algebraMap B K)).mpr he
  have hec' : algebraMap B K e * (algebraMap B K c) ^ 2 = (4 : K) := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap B K) hec
  have hdiff : a i + algebraMap B K c - a j ≠ 0 := by
    intro hzero
    apply independent_difference_ne ha hji.symm (-c)
    rw [map_neg]
    linear_combination hzero
  have hL : (lineDistancePoly (algebraMap B K e) (a j)).eval
      (a i + algebraMap B K c) ≠ 0 := by
    simpa [lineDistancePoly] using mul_ne_zero he' (pow_ne_zero 2 hdiff)
  have hL4 : (lineDistancePoly (algebraMap B K e) (a j)).eval
      (a i + algebraMap B K c) ≠ 4 := by
    intro hh
    simp only [lineDistancePoly, eval_mul, eval_C, eval_pow, eval_sub, eval_X] at hh
    have hs : (a i + algebraMap B K c - a j) ^ 2 = (algebraMap B K c) ^ 2 :=
      mul_left_cancel₀ he' (hh.trans hec'.symm)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hs | hs
    · apply independent_difference_ne ha hji.symm 0
      simp only [map_zero]
      linear_combination hs
    · apply independent_difference_ne ha hji.symm (-2 * c)
      simp only [map_mul, map_neg, map_ofNat]
      linear_combination hs
  simpa only [lineRadicandPoly, eval_mul, eval_sub, eval_ofNat, mul_ne_zero_iff,
    sub_ne_zero] using And.intro hL hL4

theorem line_radicands_squareIndependent [IsAlgClosed B]
    (e : B) (he : e ≠ 0) (anchors : List ι) (hind : anchors.Nodup)
    (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      algebraMap K[X] (RatFunc K) (lineRadicandPoly (algebraMap B K e) (a i)))) := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (4 / e) (n := 2) (by decide)
  have hce : e * c ^ 2 = 4 := by rw [hc]; field_simp
  have hce' : algebraMap B K e * (algebraMap B K c) ^ 2 = (4 : K) := by
    simpa only [map_mul, map_pow, map_ofNat] using congrArg (algebraMap B K) hce
  apply squareIndependent_of_private_simple_roots anchors hind
  intro i hi
  refine ⟨a i + algebraMap B K c,
    (line_root_simple _ _ _ hce').1, (line_root_simple _ _ _ hce').2, ?_⟩
  intro j hj hji
  exact line_root_other ha e c hce hji

theorem line_radicands_squareIndependent_over_constants [IsAlgClosed K]
    (e : B) (he : e ≠ 0) (anchors : List ι) (hind : anchors.Nodup)
    (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      algebraMap K[X] (RatFunc K) (lineRadicandPoly (algebraMap B K e) (a i)))) := by
  let E := algebraicClosure B K
  let : IsAlgClosed E := IsAlgClosure.isAlgClosed B
  have he' : algebraMap B E e ≠ 0 := (_root_.map_ne_zero _).mpr he
  have hh := line_radicands_squareIndependent (K := K) (algebraMap B E e) he'
    anchors hind ha.algebraicClosure
  have heq : algebraMap E K (algebraMap B E e) = algebraMap B K e := by
    exact (IsScalarTower.algebraMap_apply B E K e).symm
  rw [heq] at hh
  exact hh

end GenericLine

section GenericCircle

open Polynomial

variable {B : Type u} {K : Type v} [Field B] [Field K] [Algebra B K]
variable [CharZero B] [CharZero K]
variable {ι : Type*} {a : ι → K}

omit [CharZero K] in
lemma independent_affine_ne (ha : AlgebraicIndependent B a)
    {i j : ι} (hij : i ≠ j) (e c : B) :
    a j ≠ algebraMap B K e * a i + algebraMap B K c := by
  classical
  intro he
  have hp : (MvPolynomial.X j : MvPolynomial ι B) =
      MvPolynomial.C e * MvPolynomial.X i + MvPolynomial.C c := ha (by simpa using he)
  have h0 := congrArg (MvPolynomial.eval (fun _ : ι => (0 : B))) hp
  have h1 := congrArg (MvPolynomial.eval (fun k : ι => if k = j then (1 : B) else 0)) hp
  simp at h0
  simp [hij] at h1
  exact one_ne_zero (h1.trans h0.symm)

lemma circle_aux_root [IsAlgClosed B] (b : B) (hb : b ≠ 0) (hb1 : b ≠ 1) :
    ∃ q : B, q ≠ 0 ∧ b * q ^ 2 + (4 - 2 * b) * q + b = 0 ∧
      2 * b * q + 4 - 2 * b ≠ 0 := by
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq (1 - b) (n := 2) (by decide)
  have hc0 : c ≠ 0 := by
    intro he
    apply hb1
    simp only [he, zero_pow (by decide : (2 : ℕ) ≠ 0)] at hc
    exact (sub_eq_zero.mp hc.symm).symm
  let q := (b - 2 + 2 * c) / b
  have hq : b * q ^ 2 + (4 - 2 * b) * q + b = 0 := by
    dsimp [q]
    field_simp
    linear_combination 4 * hc
  have hq0 : q ≠ 0 := by
    intro he
    exact hb (by simpa [he] using hq)
  refine ⟨q, hq0, hq, ?_⟩
  have hd : 2 * b * q + 4 - 2 * b = 4 * c := by
    dsimp [q]
    field_simp
    ring
  rw [hd]
  exact mul_ne_zero (by norm_num) hc0

omit [CharZero K] in
lemma circleRadicand_eq_fraction (b u a : K) :
    circleRadicand b u a =
      algebraMap K[X] (RatFunc K) (circleRadicandNumerator b u a) /
        algebraMap K[X] (RatFunc K) (circleDenominator u a) ^ 2 := by
  simp only [circleRadicand, circleDistance, circleRadicandNumerator,
    circleDifference, map_mul, map_sub, map_ofNat]
  by_cases h : algebraMap K[X] (RatFunc K) (circleDenominator u a) = 0
  · simp [h]
  · field_simp

lemma circle_root_simple (b u a q : K) (ha : a ≠ u) (hq0 : q ≠ 0)
    (hq : b * q ^ 2 + (4 - 2 * b) * q + b = 0)
    (hd : 2 * b * q + 4 - 2 * b ≠ 0) :
    let s := u + q * (a - u)
    (circleRadicandNumerator b u a).eval s = 0 ∧
    (circleRadicandNumerator b u a).derivative.eval s ≠ 0 ∧
    (circleDenominator u a).eval s ≠ 0 := by
  dsimp only
  let s := u + q * (a - u)
  have hden : (circleDenominator u a).eval s = q * (a - u) ^ 2 := by
    simp [circleDenominator, s]
    ring
  have hden0 : (circleDenominator u a).eval s ≠ 0 := by
    rw [hden]
    exact mul_ne_zero hq0 (pow_ne_zero 2 (sub_ne_zero.mpr ha))
  have hdiff : (circleDifference b u a).eval s = 0 := by
    simp only [circleDifference, circleNumerator, circleDenominator,
      eval_sub, eval_mul, eval_neg, eval_C, eval_pow, eval_X, eval_ofNat]
    dsimp [s]
    linear_combination -(a - u) ^ 2 * hq
  have hnum : (circleNumerator b a).eval s = 4 * (circleDenominator u a).eval s := by
    simpa only [circleDifference, eval_sub, eval_mul, eval_ofNat, sub_eq_zero] using hdiff
  have hnum0 : (circleNumerator b a).eval s ≠ 0 := by
    rw [hnum]
    exact mul_ne_zero (by norm_num) hden0
  have hdif : (circleDifference b u a).derivative.eval s =
      -(2 * b * q + 4 - 2 * b) * (a - u) := by
    simp [circleDifference, circleNumerator, circleDenominator, s,
      derivative_sub, derivative_mul, derivative_pow]
    ring
  change (circleRadicandNumerator b u a).eval s = 0 ∧
    (circleRadicandNumerator b u a).derivative.eval s ≠ 0 ∧
    (circleDenominator u a).eval s ≠ 0
  refine ⟨?_, ?_, hden0⟩
  · simp [circleRadicandNumerator, hdiff]
  · simpa only [circleRadicandNumerator, derivative_mul, eval_add, eval_mul,
      hdiff, mul_zero, zero_add, hdif] using
      mul_ne_zero hnum0 (mul_ne_zero (neg_ne_zero.mpr hd) (sub_ne_zero.mpr ha))

lemma circle_root_other (ha : AlgebraicIndependent B a)
    (b u q : B) (hb : b ≠ 0) (hq0 : q ≠ 0) {i j : ι} (hji : j ≠ i) :
    let s := algebraMap B K u + algebraMap B K q * (a i - algebraMap B K u)
    (circleRadicandNumerator (algebraMap B K b) (algebraMap B K u) (a j)).eval s ≠ 0 ∧
    (circleDenominator (algebraMap B K u) (a j)).eval s ≠ 0 := by
  classical
  dsimp only
  let s := algebraMap B K u + algebraMap B K q * (a i - algebraMap B K u)
  have hai : a i ≠ algebraMap B K u := by
    intro he
    exact ha.transcendental i (he ▸ isAlgebraic_algebraMap (R := B) u)
  have haj : a j ≠ algebraMap B K u := by
    intro he
    exact ha.transcendental j (he ▸ isAlgebraic_algebraMap (R := B) u)
  have hsu : s ≠ algebraMap B K u := by
    dsimp [s]
    simpa using mul_ne_zero ((_root_.map_ne_zero (algebraMap B K)).mpr hq0) (sub_ne_zero.mpr hai)
  have hsaj : s ≠ a j := by
    intro he
    apply independent_affine_ne ha hji.symm q (u - q * u)
    rw [map_sub, map_mul]
    dsimp [s] at he
    linear_combination -he
  have hnum : (circleNumerator (algebraMap B K b) (a j)).eval s ≠ 0 := by
    simpa only [circleNumerator, eval_mul, eval_neg, eval_C, eval_pow, eval_sub, eval_X] using
      mul_ne_zero (neg_ne_zero.mpr ((_root_.map_ne_zero (algebraMap B K)).mpr hb)) (pow_ne_zero 2 (sub_ne_zero.mpr hsaj))
  have hdiff : (circleDifference (algebraMap B K b) (algebraMap B K u) (a j)).eval s ≠ 0 := by
    intro he
    let S : MvPolynomial ι B := MvPolynomial.C u + MvPolynomial.C q *
      (MvPolynomial.X i - MvPolynomial.C u)
    have hp : -MvPolynomial.C b * (S - MvPolynomial.X j) ^ 2 -
        4 * (S - MvPolynomial.C u) * (MvPolynomial.X j - MvPolynomial.C u) =
        (0 : MvPolynomial ι B) := by
      apply ha
      simpa [S, circleDifference, circleNumerator, circleDenominator, s, mul_assoc] using he
    have htest := congrArg
      (MvPolynomial.eval (fun k : ι => if k = j then u + 1 else u)) hp
    have : -b = 0 := by simpa [S, hji, hji.symm] using htest
    exact hb (neg_eq_zero.mp this)
  constructor
  · simpa [circleRadicandNumerator] using mul_ne_zero hnum hdiff
  · change (circleDenominator (algebraMap B K u) (a j)).eval s ≠ 0
    simpa only [circleDenominator, eval_mul, eval_sub, eval_X, eval_C] using
      mul_ne_zero (sub_ne_zero.mpr hsu) (sub_ne_zero.mpr haj)

theorem circle_radicands_squareIndependent [IsAlgClosed B]
    (b u : B) (hb : b ≠ 0) (hb1 : b ≠ 1)
    (anchors : List ι) (hind : anchors.Nodup) (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      circleRadicand (algebraMap B K b) (algebraMap B K u) (a i))) := by
  obtain ⟨q, hq0, hq, hd⟩ := circle_aux_root b hb hb1
  have hq0' : algebraMap B K q ≠ 0 := (_root_.map_ne_zero _).mpr hq0
  have hq' : algebraMap B K b * (algebraMap B K q) ^ 2 +
      (4 - 2 * algebraMap B K b) * algebraMap B K q + algebraMap B K b = 0 := by
    simpa only [map_add, map_mul, map_pow, map_sub, map_ofNat, map_zero] using
      congrArg (algebraMap B K) hq
  have hd' : 2 * algebraMap B K b * algebraMap B K q + 4 -
      2 * algebraMap B K b ≠ 0 := by
    simpa only [map_sub, map_add, map_mul, map_ofNat] using
      (_root_.map_ne_zero (algebraMap B K)).mpr hd
  apply squareIndependent_of_private_valuations anchors hind
  intro i hi
  have hai : a i ≠ algebraMap B K u := by
    intro he
    exact ha.transcendental i (he ▸ isAlgebraic_algebraMap (R := B) u)
  let s := algebraMap B K u + algebraMap B K q * (a i - algebraMap B K u)
  have hs := circle_root_simple (algebraMap B K b) (algebraMap B K u)
    (a i) (algebraMap B K q) hai hq0' hq' hd'
  refine ⟨pointValuation s, ?_, ?_⟩
  · rw [circleRadicand_eq_fraction, Valuation.map_div, map_pow,
      pointValuation_of_simple_root hs.1 hs.2.1,
      pointValuation_polynomial_of_eval_ne_zero hs.2.2]
    simp
  · intro j hj hji
    have hs' := circle_root_other ha b u q hb hq0 hji
    rw [circleRadicand_eq_fraction, Valuation.map_div, map_pow,
      pointValuation_polynomial_of_eval_ne_zero hs'.1,
      pointValuation_polynomial_of_eval_ne_zero hs'.2]
    simp

theorem circle_radicands_squareIndependent_over_constants [IsAlgClosed K]
    (b u : B) (hb : b ≠ 0) (hb1 : b ≠ 1)
    (anchors : List ι) (hind : anchors.Nodup) (ha : AlgebraicIndependent B a) :
    SquareIndependent (anchors.map (fun i =>
      circleRadicand (algebraMap B K b) (algebraMap B K u) (a i))) := by
  let E := algebraicClosure B K
  let : IsAlgClosed E := IsAlgClosure.isAlgClosed B
  have hb' : algebraMap B E b ≠ 0 := (_root_.map_ne_zero _).mpr hb
  have hb1' : algebraMap B E b ≠ 1 := by
    intro hh
    apply hb1
    apply (algebraMap B E).injective
    simpa using hh
  have hh := circle_radicands_squareIndependent (K := K)
    (algebraMap B E b) (algebraMap B E u) hb' hb1' anchors hind ha.algebraicClosure
  have hbe : algebraMap E K (algebraMap B E b) = algebraMap B K b :=
    (IsScalarTower.algebraMap_apply B E K b).symm
  have hue : algebraMap E K (algebraMap B E u) = algebraMap B K u :=
    (IsScalarTower.algebraMap_apply B E K u).symm
  rw [hbe, hue] at hh
  exact hh

end GenericCircle
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

lemma ratEval_comp (z : U) (hz : Transcendental K z) :
    (ratEval z hz).toRingHom.comp (algebraMap K[X] (RatFunc K)) = (aeval z).toRingHom :=
  RingHom.ext (ratEval_polynomial z hz)

@[simp] lemma ratEval_X (z : U) (hz : Transcendental K z) :
    ratEval z hz RatFunc.X=z := by
  simpa only [RatFunc.algebraMap_X,aeval_X] using ratEval_polynomial z hz (X : K[X])

@[simp] lemma ratEval_C (z : U) (hz : Transcendental K z) (a : K) :
    ratEval z hz (RatFunc.C a)=algebraMap K U a := by
  simpa only [RatFunc.algebraMap_C,aeval_C] using ratEval_polynomial z hz (C a)

lemma irreducible_fraction_curve (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) :
    Irreducible (f.map (algebraMap K[X] (RatFunc K))) :=
  (hf.isPrimitive hdeg).irreducible_iff_irreducible_map_fraction_map.mp hf

theorem exists_curve_embedding (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (z w : U) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w = 0) :
    ∃ φ : AdjoinRoot (f.map (algebraMap K[X] (RatFunc K))) →ₐ[K] U,
      Function.Injective φ ∧
      φ (AdjoinRoot.root _) = w ∧
      (∀ p : K[X], φ (AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) p)) = aeval z p) := by
  let : Fact (Irreducible (f.map (algebraMap K[X] (RatFunc K)))) :=
    ⟨irreducible_fraction_curve f hf hdeg⟩
  have hr : (f.map (algebraMap K[X] (RatFunc K))).eval₂ (ratEval z hz).toRingHom w = 0 := by
    rw [eval₂_map, ratEval_comp]
    exact hroot
  let φ := AdjoinRoot.liftAlgHom (f.map (algebraMap K[X] (RatFunc K))) (ratEval z hz) w hr
  exact ⟨φ, φ.injective, AdjoinRoot.liftAlgHom_root _ _ _ _,
    fun p => (AdjoinRoot.liftAlgHom_of _ _ _ _ _).trans (ratEval_polynomial z hz p)⟩

lemma fiber_separable [CharZero K] (f : K[X][X]) (hf : Irreducible f)
    (hdeg : f.natDegree ≠ 0) (a : U) (ha : Transcendental K a) :
    (f.map (aeval a).toRingHom).Separable := by
  have hs := (irreducible_fraction_curve f hf hdeg).separable.map
    (f := (ratEval a ha).toRingHom)
  rwa [map_map, ratEval_comp] at hs

lemma fiber_degree (f : K[X][X]) (a : U) (ha : Transcendental K a) :
    (f.map (aeval a).toRingHom).natDegree = f.natDegree :=
  natDegree_map_eq_of_injective (transcendental_iff_injective.mp ha) f

lemma fiber_leadingCoeff_ne_zero (f : K[X][X]) (hf : f ≠ 0)
    (a : U) (ha : Transcendental K a) : aeval a f.leadingCoeff ≠ 0 := by
  intro he
  apply leadingCoeff_ne_zero.mpr hf
  exact transcendental_iff_injective.mp ha (he.trans (map_zero _).symm)

lemma separable_exists_root_ne [IsAlgClosed U] (p : U[X])
    (hs : p.Separable) (hd : 2 ≤ p.natDegree) (c : U) :
    ∃ b : U, p.eval b = 0 ∧ b ≠ c := by
  classical
  have hp : p ≠ 0 := by intro hp; simp [hp] at hd
  have hc : p.roots.toFinset.card = p.natDegree := by
    rw [Multiset.toFinset_card_of_nodup (nodup_roots hs), IsAlgClosed.card_roots_eq_natDegree]
  by_contra! hn
  have hsub : p.roots.toFinset ⊆ {c} := by
    intro b hb
    simp only [Finset.mem_singleton]
    apply hn b
    exact (mem_roots hp).mp (Multiset.mem_toFinset.mp hb)
  have hcard := Finset.card_le_card hsub
  rw [hc, Finset.card_singleton] at hcard
  omega

theorem exists_distinct_smooth_sheet [CharZero K] [IsAlgClosed U]
    (f : K[X][X]) (hf : Irreducible f) (hdeg : f.natDegree ≠ 0)
    (a c : U) (ha : Transcendental K a)
    (halt : f.eval₂ (aeval a).toRingHom c ≠ 0 ∨ 2 ≤ f.natDegree) :
    ∃ b : U, f.eval₂ (aeval a).toRingHom b = 0 ∧
      f.derivative.eval₂ (aeval a).toRingHom b ≠ 0 ∧ b ≠ c := by
  let p := f.map (aeval a).toRingHom
  have hs : p.Separable := fiber_separable f hf hdeg a ha
  have hd : p.natDegree = f.natDegree := fiber_degree f a ha
  obtain ⟨b, hb, hbc⟩ : ∃ b : U, p.eval b = 0 ∧ b ≠ c := by
    rcases halt with hnc | htwo
    · obtain ⟨b, hb⟩ := IsAlgClosed.exists_root p (fun h => (hd.trans_ne hdeg) (natDegree_eq_zero_iff_degree_le_zero.mpr h.le))
      change p.eval b = 0 at hb
      refine ⟨b, hb, ?_⟩
      intro he
      subst b
      exact hnc (by simpa only [p, eval_map] using hb)
    · exact separable_exists_root_ne p hs (hd ▸ htwo) c
  refine ⟨b, ?_, ?_, hbc⟩
  · simpa only [p, eval_map] using hb
  · have hh := hs.eval₂_derivative_ne_zero (RingHom.id U) (x := b) (by simpa using hb)
    simpa only [eval₂_id, p, derivative_map, eval_map] using hh

end PlanarUnitDistances.GenericCurve

namespace PlanarUnitDistances.Radicals
open Polynomial
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

theorem line_differential_obstruction (D : Derivation k L L)
    (e e' : B) (he : e ≠ 0)
    (z w : L) (hz : Transcendental K z)
    (hw : w=algebraMap K L (algebraMap B K e)*z+algebraMap K L (algebraMap B K e'))
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, b i=algebraMap B K e*a i+algebraMap B K e')
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=
      2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  let f : RatFunc K →+* L := (GenericCurve.ratEval z hz).toRingHom
  have hfX : f RatFunc.X=z := GenericCurve.ratEval_X z hz
  have hfC (q : K) : f (RatFunc.C q)=algebraMap K L q := GenericCurve.ratEval_C z hz q
  let w' : RatFunc K := RatFunc.C (algebraMap B K e)*RatFunc.X+RatFunc.C (algebraMap B K e')
  have hfw : f w'=w := by simpa only [w',map_add,map_mul,hfC,hfX] using hw.symm
  have hind := line_radicands_squareIndependent_over_constants e he
    (List.ofFn (id : Fin 4 → Fin 4)) (List.nodup_ofFn.mpr Function.injective_id) ha
  have hd (i : Fin 4) :
      (RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))=
        algebraMap K[X] (RatFunc K) (lineDistancePoly (algebraMap B K e) (a i)) := by
    simp only [hb,w',lineDistancePoly,map_mul,map_pow,map_sub,RatFunc.algebraMap_C,
      RatFunc.algebraMap_X,map_add]
    ring
  have hind' : SquareIndependent (List.ofFn (fun i : Fin 4 =>
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i)))*
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))-4))) := by
    simpa only [hd,lineRadicandPoly,List.map_ofFn,Function.comp_def,id_eq,
      map_mul,map_sub,map_ofNat] using hind
  apply differential_distance_obstruction D f RatFunc.X w'
    (RatFunc.C ∘ a) (RatFunc.C ∘ b) (RatFunc.C ∘ da) (RatFunc.C ∘ db)
    (RatFunc.C ∘ t) l A hind' hl
  · intro i; simpa only [hfX,hfw,Function.comp_apply,hfC] using hdist i
  · intro i; simpa only [Function.comp_apply,hfC] using hda i
  · intro i; simpa only [Function.comp_apply,hfC] using hdb i
  · intro i; simpa only [Function.comp_apply,hfC] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.Radicals
open Polynomial
universe u
variable {K : Type u} [Field K]

lemma circleDistance_is_locus_distance (b u v a e : K) (ha : a ≠ u)
    (he : (a-u)*(e-v)=b) :
    (RatFunc.X-RatFunc.C a)*
      (RatFunc.C v+RatFunc.C b/(RatFunc.X-RatFunc.C u)-RatFunc.C e)=
      circleDistance b u a := by
  have he' : e=v+b/(a-u) := by
    apply (mul_left_cancel₀ (sub_ne_zero.mpr ha))
    field_simp
    linear_combination he
  have hX : (RatFunc.X : RatFunc K)-RatFunc.C u ≠ 0 := ratFunc_X_sub_C_ne_zero u
  have ha' : RatFunc.C a-RatFunc.C u ≠ 0 := by
    rw [← map_sub]
    exact (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr ha)
  rw [he']
  simp only [circleDistance,circleNumerator,circleDenominator,
    map_mul,map_neg,map_pow,map_sub,map_add,map_div₀,
    RatFunc.algebraMap_C,RatFunc.algebraMap_X]
  field_simp
  ring

variable {k B L : Type u} [Field k] [Field B] [CharZero B] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

theorem circle_differential_obstruction (D : Derivation k L L)
    (u v b₀ : B) (hb₀ : b₀ ≠ 0) (hb₁ : b₀ ≠ 1)
    (z w : L) (hz : Transcendental K z)
    (hw : (z-algebraMap K L (algebraMap B K u))*
      (w-algebraMap K L (algebraMap B K v))=algebraMap K L (algebraMap B K b₀))
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, (a i-algebraMap B K u)*(b i-algebraMap B K v)=algebraMap B K b₀)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i ≠ 0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=
      2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i) ≠ 0) : False := by
  let f : RatFunc K →+* L := (GenericCurve.ratEval z hz).toRingHom
  have hfX : f RatFunc.X=z := GenericCurve.ratEval_X z hz
  have hfC (q : K) : f (RatFunc.C q)=algebraMap K L q := GenericCurve.ratEval_C z hz q
  let w' : RatFunc K := RatFunc.C (algebraMap B K v)+
    RatFunc.C (algebraMap B K b₀)/(RatFunc.X-RatFunc.C (algebraMap B K u))
  have hz' : z-algebraMap K L (algebraMap B K u) ≠ 0 := by
    intro hh
    apply hz
    rw [sub_eq_zero.mp hh]
    exact isAlgebraic_algebraMap _
  have hfw : f w'=w := by
    simp only [w',map_add,map_div₀,map_sub,hfC,hfX]
    apply mul_left_cancel₀ hz'
    field_simp
    linear_combination -hw
  have hind := circle_radicands_squareIndependent_over_constants b₀ u hb₀ hb₁
    (List.ofFn (id : Fin 4 → Fin 4)) (List.nodup_ofFn.mpr Function.injective_id) ha
  have hd (i : Fin 4) :
      (RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))=
        circleDistance (algebraMap B K b₀) (algebraMap B K u) (a i) := by
    apply circleDistance_is_locus_distance _ _ _ _ _ _ (hb i)
    intro hh
    exact ha.transcendental i (hh ▸ isAlgebraic_algebraMap u)
  have hind' : SquareIndependent (List.ofFn (fun i : Fin 4 =>
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i)))*
      ((RatFunc.X-RatFunc.C (a i))*(w'-RatFunc.C (b i))-4))) := by
    simpa only [hd,circleRadicand,List.map_ofFn,Function.comp_def,id_eq] using hind
  apply differential_distance_obstruction D f RatFunc.X w'
    (RatFunc.C ∘ a) (RatFunc.C ∘ b) (RatFunc.C ∘ da) (RatFunc.C ∘ db)
    (RatFunc.C ∘ t) l A hind' hl
  · intro i; simpa only [hfX,hfw,Function.comp_apply,hfC] using hdist i
  · intro i; simpa only [Function.comp_apply,hfC] using hda i
  · intro i; simpa only [Function.comp_apply,hfC] using hdb i
  · intro i; simpa only [Function.comp_apply,hfC] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

end OAI
end

section
-- module Solutions.OAIQ2_Uni.UnitDistances_GenericCurves
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace PlanarUnitDistances.GenericNoncoincidence
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

lemma poleTest_eval_center (f : K[X][X]) (a b k : K)
    (hlead : f.leadingCoeff.eval a ≠ 0) :
    (poleTest f a b k).eval a = f.leadingCoeff.eval a * k ^ f.natDegree := by
  change (evalRingHom a) ((f.scaleRoots (X - C a)).eval
    (C b * (X - C a) + C k)) = _
  rw [← eval₂_at_apply (evalRingHom a)]
  simp only [coe_evalRingHom, eval_add, eval_mul, eval_C, eval_sub, eval_X, sub_self, mul_zero,
    zero_add]
  rw [← eval_map, map_scaleRoots f (X - C a) (evalRingHom a) hlead]
  simp only [coe_evalRingHom, eval_sub, eval_X, eval_C, sub_self, scaleRoots_zero,
    eval_smul, eval_pow, eval_X, smul_eq_mul,
    leadingCoeff_map_of_leadingCoeff_ne_zero (evalRingHom a) hlead,
    natDegree_map_of_leadingCoeff_ne_zero (evalRingHom a) hlead]

lemma poleTest_nonzero (f : K[X][X]) (a b k : K)
    (hlead : f.leadingCoeff.eval a ≠ 0) (hk : k ≠ 0) :
    poleTest f a b k ≠ 0 := by
  intro h
  have he := poleTest_eval_center f a b k hlead
  rw [h, eval_zero] at he
  exact mul_ne_zero hlead (pow_ne_zero _ hk) he.symm

theorem distance_ne_nonzero (f : K[X][X]) (a b k : K)
    (hlead : f.leadingCoeff.eval a ≠ 0) (hk : k ≠ 0)
    (d e : U) (hd : Transcendental K d)
    (hroot : f.eval₂ (aeval d).toRingHom e = 0) :
    (algebraMap K U a - d) * (algebraMap K U b - e) ≠ algebraMap K U k := by
  intro he
  have hmul : (aeval d) (C b * (X - C a) + C k) =
      (aeval d) (X - C a) * e := by
    simp only [map_add, map_mul, map_sub, aeval_C, aeval_X]
    linear_combination -he
  have hzero : aeval d (poleTest f a b k) = 0 := by
    change (aeval d).toRingHom ((f.scaleRoots (X - C a)).eval
      (C b * (X - C a) + C k)) = 0
    rw [← eval₂_at_apply (aeval d).toRingHom]
    change (f.scaleRoots (X - C a)).eval₂ (aeval d).toRingHom
      ((aeval d) (C b * (X - C a) + C k)) = 0
    rw [hmul]
    exact scaleRoots_eval₂_eq_zero (aeval d).toRingHom hroot
  exact poleTest_nonzero f a b k hlead hk
    (transcendental_iff_injective.mp hd (hzero.trans (map_zero _).symm))

lemma primitive_fiber_ne_zero (g : K[X][X]) (hg : g.IsPrimitive) (b : U) :
    g.map (aeval b).toRingHom ≠ 0 := by
  intro hz
  apply minpoly.not_isUnit K b
  apply hg
  rw [C_dvd_iff_dvd_coeff]
  intro n
  apply minpoly.dvd K b
  have hh := congrArg (fun p : U[X] => p.coeff n) hz
  simpa only [coeff_map, coeff_zero, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] using hh

lemma aevalAeval_eq_eval₂ (x y : U) (p : K[X][X]) :
    p.aevalAeval x y = p.eval₂ (aeval x).toRingHom y := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, eval₂_add, hp, hq]
  | monomial n p =>
    rw [← C_mul_X_pow_eq_monomial]
    simp only [map_mul, map_pow, aevalAeval_C, aevalAeval_Y,
      eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rfl

theorem generic_ordinate_ne_constant (f : K[X][X])
    (hf : (Bivariate.swap f).IsPrimitive) (b : K)
    (d e : U) (hd : Transcendental K d)
    (hroot : f.aevalAeval d e = 0) : e ≠ algebraMap K U b := by
  intro he
  let g : K[X] := (Bivariate.swap f).map (aeval b).toRingHom
  have hg : g ≠ 0 := primitive_fiber_ne_zero (Bivariate.swap f) hf b
  have heval : aeval d g = 0 := by
    have hs := Bivariate.aevalAeval_swap (algebraMap K U b) d f
    rw [he] at hroot
    rw [hroot] at hs
    have hh : (algebraMap K U).comp (aeval b : K[X] →ₐ[K] K).toRingHom =
        (aeval (algebraMap K U b) : K[X] →ₐ[K] U).toRingHom := by
      ext c <;> simp
    rw [aevalAeval_eq_eval₂] at hs
    simpa only [g, aeval_def, eval₂_map, hh] using hs
  exact hg (transcendental_iff_injective.mp hd (heval.trans (map_zero _).symm))

end PlanarUnitDistances.GenericNoncoincidence

namespace PlanarUnitDistances.BivariateMaps
open Polynomial
variable {B K L : Type*} [Field B] [Field K] [Field L]

lemma bimap_injective (φ : B →+* K) : Function.Injective (bimap φ) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ φ.injective)

lemma isUnit_bimap_iff (φ : B →+* K) (p : B[X][X]) :
    IsUnit (bimap φ p) ↔ IsUnit p := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := Polynomial.isUnit_iff.mp h
    obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hq
    have he' : bimap φ p=bimap φ (C (C ((p.coeff 0).coeff 0))) := by
      have hcoeff := congrArg (fun p : K[X][X] => (p.coeff 0).coeff 0) he
      simp only [bimap,coe_mapRingHom,coeff_map,coeff_C_zero] at hcoeff
      simpa only [bimap,coe_mapRingHom,map_C,hcoeff] using he.symm
    have hp := bimap_injective φ he'
    have hn : (p.coeff 0).coeff 0 ≠ 0 := by
      intro hz
      have hcoeff := congrArg (fun p : K[X][X] => (p.coeff 0).coeff 0) he
      simp only [bimap,coe_mapRingHom,coeff_map,coeff_C_zero,hz,map_zero] at hcoeff
      exact hc.ne_zero hcoeff
    rw [hp]
    exact isUnit_C.mpr <| isUnit_C.mpr <| isUnit_iff_ne_zero.mpr hn
  · exact fun h => h.map (bimap φ)

lemma irreducible_of_bimap (φ : B →+* K) {p : B[X][X]}
    (h : Irreducible (bimap φ p)) : Irreducible p := by
  refine ⟨fun hu => h.not_isUnit (hu.map _), ?_⟩
  intro a b he
  rcases h.isUnit_or_isUnit (by simpa only [map_mul] using congrArg (bimap φ) he)
    with ha|hb
  · exact Or.inl ((isUnit_bimap_iff φ a).mp ha)
  · exact Or.inr ((isUnit_bimap_iff φ b).mp hb)

lemma bimap_comp (φ : B →+* K) (ψ : K →+* L) (p : B[X][X]) :
    bimap ψ (bimap φ p)=bimap (ψ.comp φ) p := by
  simp only [bimap, coe_mapRingHom, map_map, mapRingHom_comp]

lemma bimap_natDegree (φ : B →+* K) (p : B[X][X]) :
    (bimap φ p).natDegree=p.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ φ.injective) _

lemma bimap_swap (φ : B →+* K) (p : B[X][X]) :
    Bivariate.swap (bimap φ p)=bimap φ (Bivariate.swap p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial m c =>
      simp only [bimap,coe_mapRingHom,map_monomial,Bivariate.swap_monomial_monomial]

lemma eval_bimap [Algebra B K] [Algebra B L] [Algebra K L] [IsScalarTower B K L]
    (p : B[X][X]) (x y : L) :
    (bimap (algebraMap B K) p).eval₂ (aeval x).toRingHom y =
      p.eval₂ (aeval x).toRingHom y := by
  simp only [bimap,coe_mapRingHom,eval₂_map]
  congr 1
  ext c <;> simp [IsScalarTower.algebraMap_apply B K L]

end PlanarUnitDistances.BivariateMaps

namespace PlanarUnitDistances.GenericSheets
open Polynomial BivariateMaps
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma fiber_algebraic (f : B[X][X]) (hf : f ≠ 0)
    (a b : K) (ha : Transcendental B a)
    (hroot : f.eval₂ (aeval a).toRingHom b = 0) :
    IsAlgebraic (IntermediateField.adjoin B ({a} : Set K)) b := by
  let E := IntermediateField.adjoin B ({a} : Set K)
  let a' : E := ⟨a, IntermediateField.subset_adjoin B _ (Set.mem_singleton _)⟩
  have ha' : Transcendental B a' := by
    intro h
    exact ha (h.algHom E.val)
  let q := f.map (aeval a').toRingHom
  refine ⟨q, ?_, ?_⟩
  · exact fun he => hf (Polynomial.map_injective _ (transcendental_iff_injective.mp ha')
      (he.trans (Polynomial.map_zero _).symm))
  · have hh : (algebraMap E K).comp (aeval a' : B[X] →ₐ[B] E).toRingHom=(aeval a : B[X] →ₐ[B] K).toRingHom := by
      ext c <;> simp [a']
    change q.eval₂ (algebraMap E K) b=0
    dsimp only [q]
    rw [eval₂_map,hh]
    exact hroot

lemma other_transcendental {ι : Type*} {a : ι → K} (ha : AlgebraicIndependent B a)
    {i j : ι} (hji : j ≠ i) :
    Transcendental (algebraicClosure (IntermediateField.adjoin B ({a i} : Set K)) K) (a j) := by
  apply Transcendental.algebraicClosure
  apply IntermediateField.transcendental_adjoin_iff.mpr
  have hh := ha.transcendental_adjoin (s := {i}) (i := j) (by simpa using hji)
  rw [Set.image_singleton] at hh
  exact hh

theorem exists_private_sheet_curve [CharZero B] [CharZero K] [IsAlgClosed K]
    {ι : Type*} (f g : B[X][X]) (hf : Irreducible f) (hfdeg : f.natDegree ≠ 0)
    (hgK : Irreducible (bimap (algebraMap B K) g))
    (hgswap : (Bivariate.swap g).natDegree ≠ 0)
    (a c : ι → K) (ha : AlgebraicIndependent B a)
    (hc : ∀ i, g.eval₂ (aeval (a i)).toRingHom (c i)=0)
    (i : ι) (halt : f.eval₂ (aeval (a i)).toRingHom (c i) ≠ 0 ∨ 2 ≤ f.natDegree) :
    ∃ b : K, f.eval₂ (aeval (a i)).toRingHom b=0 ∧
      f.derivative.eval₂ (aeval (a i)).toRingHom b≠0 ∧ b≠c i ∧
      ∀ j, j≠i → (a i-a j)*(b-c j)≠0 ∧ (a i-a j)*(b-c j)≠4 := by
  obtain ⟨b,hb,hbd,hbc⟩ := GenericCurve.exists_distinct_smooth_sheet f hf hfdeg
    (a i) (c i) (ha.transcendental i) halt
  refine ⟨b,hb,hbd,hbc,?_⟩
  let F := IntermediateField.adjoin B ({a i} : Set K)
  let E := algebraicClosure F K
  let : IsScalarTower B E K := IsScalarTower.of_algebraMap_eq fun _ => rfl
  let ai : F := ⟨a i, IntermediateField.subset_adjoin B _ (Set.mem_singleton _)⟩
  let a' : E := algebraMap F E ai
  have ha' : algebraMap E K a'=a i := by simp [a',ai]
  have hbalg : IsAlgebraic F b := fiber_algebraic f hf.ne_zero (a i) b (ha.transcendental i) hb
  let b' : E := ⟨b, mem_algebraicClosure_iff.mpr hbalg⟩
  let g' := bimap (algebraMap B E) g
  have hge : bimap (algebraMap E K) g'=bimap (algebraMap B K) g := by
    simp only [g',bimap_comp,← IsScalarTower.algebraMap_eq B E K]
  have hg' : Irreducible g' := irreducible_of_bimap (algebraMap E K) (hge.symm ▸ hgK)
  have hgs' : (Bivariate.swap g').IsPrimitive := by
    apply ((MulEquiv.irreducible_iff Bivariate.swap).mpr hg').isPrimitive
    simpa only [g',bimap_swap,bimap_natDegree] using hgswap
  have hlead : g'.leadingCoeff.eval a' ≠ 0 := by
    intro hz
    have hz' := congrArg (algebraMap E K) hz
    have hg0 : g ≠ 0 := (irreducible_of_bimap (algebraMap B K) hgK).ne_zero
    apply GenericCurve.fiber_leadingCoeff_ne_zero g hg0 (a i) (ha.transcendental i)
    have hh : algebraMap E K (g'.leadingCoeff.eval a')=aeval (a i) g.leadingCoeff := by
      dsimp only [g', BivariateMaps.bimap,coe_mapRingHom]
      rw [leadingCoeff_map_of_injective (f := Polynomial.mapRingHom (algebraMap B E))
        (Polynomial.map_injective _ (algebraMap B E).injective)]
      change algebraMap E K ((g.leadingCoeff.map (algebraMap B E)).eval a')=_
      rw [← eval₂_hom, eval₂_map, ← IsScalarTower.algebraMap_eq B E K,ha',← aeval_def]
    simpa only [hh,map_zero] using hz'
  intro j hji
  have haj : Transcendental E (a j) := other_transcendental ha hji
  have hcj : g'.eval₂ (aeval (a j)).toRingHom (c j)=0 := by
    simpa only [g',eval_bimap] using hc j
  have hcz : c j≠(b' : K) :=
    GenericNoncoincidence.generic_ordinate_ne_constant g' hgs' b' (a j) (c j) haj
      (by simpa only [GenericNoncoincidence.aevalAeval_eq_eval₂] using hcj)
  have hdz : a i ≠ a j := fun hh => hji (ha.injective hh).symm
  refine ⟨mul_ne_zero (sub_ne_zero.mpr hdz) (sub_ne_zero.mpr hcz.symm),?_⟩
  have hn := GenericNoncoincidence.distance_ne_nonzero g' a' b' (4 : E) hlead
    (by norm_num) (a j) (c j) haj hcj
  simpa only [map_ofNat,ha',show algebraMap E K b'=b from rfl] using hn

end PlanarUnitDistances.GenericSheets

namespace PlanarUnitDistances.CurveValuations

universe u
variable {K : Type u} [Field K]

open Polynomial

theorem powerSeries_simple_root (f : (PowerSeries K)[X])
    (hlc : IsUnit f.leadingCoeff) (b : K)
    (hroot : f.eval₂ (PowerSeries.constantCoeff) b = 0)
    (hderiv : f.derivative.eval₂ (PowerSeries.constantCoeff) b ≠ 0) :
    ∃ w : PowerSeries K, f.eval w = 0 ∧ PowerSeries.constantCoeff w = b := by
  let I : Ideal (PowerSeries K) := Ideal.span {PowerSeries.X}
  let u : (PowerSeries K)ˣ := hlc.unit
  let g : (PowerSeries K)[X] := u⁻¹ • f
  have hg : g.Monic := monic_of_isUnit_leadingCoeff_inv_smul hlc
  have hb : g.eval (PowerSeries.C b) ∈ I := by
    rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]
    simp only [g, Units.smul_def, eval_smul, smul_eq_mul, map_mul]
    rw [← eval₂_at_apply]
    simp only [PowerSeries.constantCoeff_C, hroot, mul_zero]
  have hd : IsUnit (g.derivative.eval (PowerSeries.C b)) := by
    apply PowerSeries.isUnit_iff_constantCoeff.mpr
    simp only [g, Units.smul_def, derivative_smul, eval_smul, smul_eq_mul, map_mul]
    apply IsUnit.mul
    · exact (u⁻¹).isUnit.map PowerSeries.constantCoeff
    · apply isUnit_iff_ne_zero.mpr
      simpa only [← eval₂_at_apply, PowerSeries.constantCoeff_C] using hderiv
  obtain ⟨w, hw, hwmod⟩ := HenselianRing.is_henselian g hg (PowerSeries.C b) hb
    (hd.map (Ideal.Quotient.mk I))
  refine ⟨w, ?_, ?_⟩
  · change g.eval w = 0 at hw
    simpa [g, Units.smul_def] using hw
  · rw [Ideal.mem_span_singleton, PowerSeries.X_dvd_iff, map_sub,
      PowerSeries.constantCoeff_C, sub_eq_zero] at hwmod
    exact hwmod

open scoped LaurentSeries nonZeroDivisors

lemma constantCoeff_comp_shiftPowerSeries (a : K) :
    PowerSeries.constantCoeff.comp (shiftPowerSeries a) = evalRingHom a := by
  ext c <;> simp

@[simp] lemma constantCoeff_shiftPowerSeries (a : K) (p : K[X]) :
    PowerSeries.constantCoeff (shiftPowerSeries a p) = p.eval a :=
  congrArg (fun φ : K[X] →+* K => φ p) (constantCoeff_comp_shiftPowerSeries a)

lemma shiftRatFunc_comp_algebraMap (a : K) :
    (shiftRatFunc a).comp (algebraMap K[X] (RatFunc K)) = shiftLaurent a := by
  exact RingHom.ext (shiftRatFunc_polynomial a)

theorem exists_smooth_branch (f : K[X][X]) (a b : K)
    (hlead : f.leadingCoeff.eval a ≠ 0)
    (hroot : f.eval₂ (evalRingHom a) b = 0)
    (hderiv : f.derivative.eval₂ (evalRingHom a) b ≠ 0) :
    ∃ w : PowerSeries K,
      (f.map (shiftPowerSeries a)).eval w = 0 ∧ PowerSeries.constantCoeff w = b := by
  apply powerSeries_simple_root
  · apply PowerSeries.isUnit_iff_constantCoeff.mpr
    rw [leadingCoeff_map_of_injective (shiftPowerSeries_injective a),
      constantCoeff_shiftPowerSeries]
    exact isUnit_iff_ne_zero.mpr hlead
  · simpa only [eval₂_map, constantCoeff_comp_shiftPowerSeries] using hroot
  · simpa only [derivative_map, eval₂_map, constantCoeff_comp_shiftPowerSeries] using hderiv

theorem exists_curve_branch_map (f : K[X][X]) (a b : K)
    (hlead : f.leadingCoeff.eval a ≠ 0)
    (hroot : f.eval₂ (evalRingHom a) b = 0)
    (hderiv : f.derivative.eval₂ (evalRingHom a) b ≠ 0) :
    ∃ (w : PowerSeries K) (φ : CurveField f →+* K⸨X⸩),
      PowerSeries.constantCoeff w = b ∧
      φ (AdjoinRoot.root _) = HahnSeries.ofPowerSeries ℤ K w ∧
      φ.comp (AdjoinRoot.of _) = shiftRatFunc a := by
  obtain ⟨w, hw, hwc⟩ := exists_smooth_branch f a b hlead hroot hderiv
  have he : (f.map (algebraMap K[X] (RatFunc K))).eval₂ (shiftRatFunc a)
      (HahnSeries.ofPowerSeries ℤ K w) = 0 := by
    rw [eval₂_map, shiftRatFunc_comp_algebraMap]
    have hh := congrArg (HahnSeries.ofPowerSeries ℤ K) hw
    simpa only [map_zero, ← eval₂_at_apply, eval₂_map, shiftLaurent] using hh
  exact ⟨w, AdjoinRoot.lift (shiftRatFunc a) (HahnSeries.ofPowerSeries ℤ K w) he,
    hwc, AdjoinRoot.lift_root he, AdjoinRoot.lift_comp_of he⟩

open WithZero Multiplicative

lemma laurent_valuation_powerSeries_unit {w : PowerSeries K}
    (hw : PowerSeries.constantCoeff w ≠ 0) :
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) (HahnSeries.ofPowerSeries ℤ K w) = 1 := by
  rw [LaurentSeries.valuation_def, ← LaurentSeries.coe_algebraMap]
  apply (IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem
    (PowerSeries.idealX K)).mpr
  simpa [PowerSeries.idealX, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff] using hw

lemma laurent_valuation_powerSeries_X :
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰)
      (HahnSeries.ofPowerSeries ℤ K PowerSeries.X) = WithZero.exp (-1 : ℤ) := by
  simpa using LaurentSeries.valuation_X_pow K 1

lemma curve_branch_map_of {f : K[X][X]} {a : K} {φ : CurveField f →+* K⸨X⸩}
    (hφ : φ.comp (AdjoinRoot.of _) = shiftRatFunc a) (p : K[X]) :
    φ (AdjoinRoot.of _ (algebraMap K[X] (RatFunc K) p)) = shiftLaurent a p := by
  have hh := congrArg (fun ψ : RatFunc K →+* K⸨X⸩ =>
    ψ (algebraMap K[X] (RatFunc K) p)) hφ
  simpa only [RingHom.comp_apply, shiftRatFunc_polynomial] using hh

lemma curve_branch_map_L {f : K[X][X]} {a : K} {w : PowerSeries K}
    {φ : CurveField f →+* K⸨X⸩}
    (hφ : φ.comp (AdjoinRoot.of _) = shiftRatFunc a)
    (hwφ : φ (AdjoinRoot.root _) = HahnSeries.ofPowerSeries ℤ K w) (d c : K) :
    φ (curveL f d c) = HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X + PowerSeries.C (a-d)) * (w - PowerSeries.C c)) := by
  simp only [curveL, map_mul, map_sub, curveZ, curveC,
    curve_branch_map_of hφ, hwφ, shiftLaurent, RingHom.comp_apply,
    shiftPowerSeries_X, shiftPowerSeries_C]
  simp only [← map_sub, ← map_mul]
  congr 2
  simp only [map_sub]
  ring

theorem exists_curve_private_valuation [CharZero K]
    (f : K[X][X]) (a b c : K)
    (hlead : f.leadingCoeff.eval a ≠ 0)
    (hroot : f.eval₂ (evalRingHom a) b = 0)
    (hderiv : f.derivative.eval₂ (evalRingHom a) b ≠ 0)
    (hbc : b ≠ c) :
    ∃ v : Valuation (CurveField f) ℤᵐ⁰,
      v (curveD f a c) = WithZero.exp (-1 : ℤ) ∧
      ∀ d e : K, (a-d)*(b-e) ≠ 0 → (a-d)*(b-e) ≠ 4 →
        v (curveD f d e) = 1 := by
  obtain ⟨w, φ, hw, hwφ, hφ⟩ := exists_curve_branch_map f a b hlead hroot hderiv
  let v : Valuation (CurveField f) ℤᵐ⁰ :=
    (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰).comap φ
  have hL (d e : K) : φ (curveL f d e) = HahnSeries.ofPowerSeries ℤ K
      ((PowerSeries.X + PowerSeries.C (a-d)) * (w - PowerSeries.C e)) :=
    curve_branch_map_L hφ hwφ d e
  have hval {p : PowerSeries K} (hp : PowerSeries.constantCoeff p ≠ 0) :
      (Valued.v : Valuation K⸨X⸩ ℤᵐ⁰) (HahnSeries.ofPowerSeries ℤ K p) = 1 :=
    laurent_valuation_powerSeries_unit hp
  refine ⟨v, ?_, ?_⟩
  · have hLc : v (curveL f a c) = WithZero.exp (-1 : ℤ) := by
      change Valued.v (φ (curveL f a c)) = _
      rw [hL]
      simp only [sub_self, map_zero, add_zero, map_mul]
      rw [laurent_valuation_powerSeries_X, hval, mul_one]
      simpa [hw] using sub_ne_zero.mpr hbc
    have hL4 : v (curveL f a c - 4) = 1 := by
      change Valued.v (φ (curveL f a c - 4)) = _
      rw [map_sub, hL, map_ofNat]
      rw [← map_ofNat (HahnSeries.ofPowerSeries ℤ K) 4, ← map_sub]
      apply hval
      norm_num [hw, map_ofNat]
    rw [curveD, map_mul, hLc, hL4, mul_one]
  · intro d e hne hfour
    have hLc : v (curveL f d e) = 1 := by
      change Valued.v (φ (curveL f d e)) = _
      rw [hL]
      apply hval
      simpa [hw] using hne
    have hL4 : v (curveL f d e - 4) = 1 := by
      change Valued.v (φ (curveL f d e - 4)) = _
      rw [map_sub, hL, map_ofNat]
      rw [← map_ofNat (HahnSeries.ofPowerSeries ℤ K) 4, ← map_sub]
      apply hval
      simpa [hw, map_ofNat] using sub_ne_zero.mpr hfour
    rw [curveD, map_mul, hLc, hL4, one_mul]

end PlanarUnitDistances.CurveValuations

namespace PlanarUnitDistances.Radicals
open Polynomial CurveValuations
universe u
variable {k K L : Type u} [Field k] [Field K] [CharZero K] [Field L]
  [Algebra k L] [Algebra K L]

theorem curve_differential_obstruction (D : Derivation k L L)
    (f : K[X][X]) (hf : Irreducible f) (hfdeg : f.natDegree≠0)
    (z w : L) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w=0)
    (a b da db t : Fin 4 → K)
    (hsheet : ∀ i, ∃ c : K, f.leadingCoeff.eval (a i)≠0 ∧
      f.eval₂ (evalRingHom (a i)) c=0 ∧ f.derivative.eval₂ (evalRingHom (a i)) c≠0 ∧
      c≠b i ∧ ∀ j, j≠i → (a i-a j)*(c-b j)≠0 ∧ (a i-a j)*(c-b j)≠4)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  let : Fact (Irreducible (f.map (algebraMap K[X] (RatFunc K)))) :=
    ⟨GenericCurve.irreducible_fraction_curve f hf hfdeg⟩
  let : CharZero (CurveField f) :=
    charZero_of_injective_algebraMap (algebraMap K (CurveField f)).injective
  obtain ⟨φ,hφ,hφw,hφp⟩ := GenericCurve.exists_curve_embedding f hf hfdeg z w hz hroot
  have hφz : φ (curveZ f)=z := by simpa only [curveZ,aeval_X] using hφp X
  have hφc (c : K) : φ (curveC f c)=algebraMap K L c := by
    simpa only [curveC,aeval_C] using hφp (C c)
  have hind : SquareIndependent (List.ofFn (fun i => curveD f (a i) (b i))) := by
    have hh := squareIndependent_of_private_valuations
      (List.ofFn (id : Fin 4 → Fin 4)) (List.nodup_ofFn.mpr Function.injective_id)
      (fun i => curveD f (a i) (b i)) ?_
    · simpa only [List.map_ofFn,Function.comp_def,id_eq] using hh
    intro i _
    obtain ⟨c,hlead,hc,hcd,hcb,hcs⟩ := hsheet i
    obtain ⟨v,hv,hw⟩ := exists_curve_private_valuation f (a i) c (b i) hlead hc hcd hcb
    exact ⟨v,hv,fun j _ hji => hw _ _ (hcs j hji).1 (hcs j hji).2⟩
  apply differential_distance_obstruction D φ.toRingHom (curveZ f) (AdjoinRoot.root _)
    (curveC f ∘ a) (curveC f ∘ b) (curveC f ∘ da) (curveC f ∘ db) (curveC f ∘ t)
    l A hind hl
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      hφz,hφw,Function.comp_apply,hφc] using hdist i
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Function.comp_apply,hφc] using hda i
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Function.comp_apply,hφc] using hdb i
  · intro i; simpa only [AlgHom.toRingHom_eq_coe,AlgHom.coe_toRingHom,
      Function.comp_apply,hφc] using hlog i
  · exact hD
end PlanarUnitDistances.Radicals

namespace PlanarUnitDistances.GenericSheets
open Polynomial BivariateMaps
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma mapped_leading_eval (f : B[X][X]) (a : K) :
    (bimap (algebraMap B K) f).leadingCoeff.eval a=aeval a f.leadingCoeff := by
  dsimp only [BivariateMaps.bimap,coe_mapRingHom]
  rw [leadingCoeff_map_of_injective (f := Polynomial.mapRingHom (algebraMap B K))
    (Polynomial.map_injective _ (algebraMap B K).injective)]
  change (f.leadingCoeff.map (algebraMap B K)).eval a=_
  rw [eval_map,← aeval_def]

lemma mapped_eval (f : B[X][X]) (a b : K) :
    (bimap (algebraMap B K) f).eval₂ (evalRingHom a) b=f.eval₂ (aeval a).toRingHom b := by
  have hh := BivariateMaps.eval_bimap (K := K) f a b
  have he : (aeval a : K[X] →ₐ[K] K).toRingHom=evalRingHom a := by
    ext c <;> simp
  simpa only [he] using hh

lemma mapped_derivative_eval (f : B[X][X]) (a b : K) :
    (bimap (algebraMap B K) f).derivative.eval₂ (evalRingHom a) b=
      f.derivative.eval₂ (aeval a).toRingHom b := by
  change (f.map (Polynomial.mapRingHom (algebraMap B K))).derivative.eval₂ _ _=_
  rw [derivative_map]
  exact mapped_eval f.derivative a b
end PlanarUnitDistances.GenericSheets

namespace PlanarUnitDistances.Radicals
open Polynomial BivariateMaps
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]

theorem curve_curve_differential_obstruction (D : Derivation k L L)
    (f g : B[X][X]) (hfK : Irreducible (bimap (algebraMap B K) f))
    (hfdeg : f.natDegree≠0) (hgK : Irreducible (bimap (algebraMap B K) g))
    (hgswap : (Bivariate.swap g).natDegree≠0)
    (z w : L) (hz : Transcendental K z)
    (hroot : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0)
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, g.eval₂ (aeval (a i)).toRingHom (b i)=0)
    (halt : ∀ i, f.eval₂ (aeval (a i)).toRingHom (b i)≠0 ∨ 2≤f.natDegree)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  apply curve_differential_obstruction D _ hfK (by simpa only [bimap_natDegree] using hfdeg)
    z w hz hroot a b da db t ?_ l A hl hdist hda hdb hlog hD
  intro i
  have hf := irreducible_of_bimap (algebraMap B K) hfK
  obtain ⟨c,hc,hcd,hcb,hcs⟩ := GenericSheets.exists_private_sheet_curve f g hf hfdeg hgK
    hgswap a b ha hb i (halt i)
  refine ⟨c,?_,?_,?_,hcb,hcs⟩
  · rw [GenericSheets.mapped_leading_eval]
    exact GenericCurve.fiber_leadingCoeff_ne_zero f hf.ne_zero (a i) (ha.transcendental i)
  · simpa only [GenericSheets.mapped_eval] using hc
  · simpa only [GenericSheets.mapped_derivative_eval] using hcd

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

lemma coeff_swap (f : K[X][X]) (i j : ℕ) :
    ((Bivariate.swap f).coeff i).coeff j=(f.coeff j).coeff i := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [map_add,coeff_add,hf,hg]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,coeff_add,hp,hq]
    | monomial m a =>
      rw [Bivariate.swap_monomial_monomial]
      simp only [coeff_monomial]
      split_ifs <;> simp_all [coeff_monomial]

lemma coeff_natDegree_le_swap (f : K[X][X]) (i : ℕ) :
    (f.coeff i).natDegree ≤ (Bivariate.swap f).natDegree := by
  by_cases hi : f.coeff i=0
  · simp [hi]
  apply le_natDegree_of_ne_zero
  intro hz
  apply leadingCoeff_ne_zero.mpr hi
  have hh := congrArg (fun p : K[X] => p.coeff i) hz
  simpa only [coeff_zero,coeff_swap,coeff_natDegree] using hh

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

end PlanarUnitDistances.BivariateDegree

namespace PlanarUnitDistances.BiAffine
open Polynomial
variable {K U : Type*} [Field K] [Field U] [Algebra K U]

lemma expansion (f : K[X][X]) (hw : f.natDegree ≤ 1)
    (hz : (Bivariate.swap f).natDegree ≤ 1) :
    f = C (C ((f.coeff 1).coeff 1)*X+C ((f.coeff 1).coeff 0))*X+
      C (C ((f.coeff 0).coeff 1)*X+C ((f.coeff 0).coeff 0)) := by
  have h1 := eq_X_add_C_of_natDegree_le_one
    ((BivariateDegree.coeff_natDegree_le_swap f 1).trans hz)
  have h0 := eq_X_add_C_of_natDegree_le_one
    ((BivariateDegree.coeff_natDegree_le_swap f 0).trans hz)
  calc
    f = C (f.coeff 1)*X+C (f.coeff 0) := eq_X_add_C_of_natDegree_le_one hw
    _ = _ := congrArg₂ (fun p q : K[X] => C p*X+C q) h1 h0

lemma linear_not_unit {a d : K} (ha : a ≠ 0) : ¬ IsUnit (C a*X+C d) := by
  apply not_isUnit_of_natDegree_pos
  have hh : (C a*X+C d).coeff 1 ≠ 0 := by simpa using ha
  exact lt_of_lt_of_le (by decide : 0<1) (le_natDegree_of_ne_zero hh)

lemma determinant_ne_zero (f : K[X][X]) (hf : Irreducible f)
    (hw : f.natDegree ≤ 1) (hz : (Bivariate.swap f).natDegree ≤ 1)
    (ha : (f.coeff 1).coeff 1 ≠ 0) :
    (f.coeff 1).coeff 1*(f.coeff 0).coeff 0 ≠
      (f.coeff 0).coeff 1*(f.coeff 1).coeff 0 := by
  let a := (f.coeff 1).coeff 1
  let c := (f.coeff 0).coeff 1
  let d := (f.coeff 1).coeff 0
  let e := (f.coeff 0).coeff 0
  change a ≠ 0 at ha
  intro he
  have he' : d*(c/a)=e := by
    rw [← mul_div_assoc, div_eq_iff ha]
    change a*e=c*d at he
    linear_combination -he
  have hac : a*(c/a)=c := by field_simp
  have hp : C c*X+C e=(C a*X+C d)*C (c/a) := by
    rw [add_mul,mul_assoc,mul_comm X,← mul_assoc,← C_mul,← C_mul,hac,he']
  have hex : f=C (C a*X+C d)*(X+C (C (c/a))) := by
    rw [expansion f hw hz]
    change C (C a*X+C d)*X+C (C c*X+C e)=_
    rw [mul_add,← C_mul,hp]
  rcases hf.isUnit_or_isUnit hex with hl | hr
  · exact linear_not_unit ha (isUnit_C.mp hl)
  · exact not_isUnit_of_natDegree_pos _ (by simp) hr

theorem line_or_circle (f : K[X][X]) (hf : Irreducible f)
    (hw : f.natDegree=1) (hz : (Bivariate.swap f).natDegree=1) :
    (∃ e e' : K, e ≠ 0 ∧ ∀ z w : U,
      f.eval₂ (aeval z).toRingHom w=0 ↔ w=algebraMap K U e*z+algebraMap K U e') ∨
    (∃ u v b : K, b ≠ 0 ∧ ∀ z w : U,
      f.eval₂ (aeval z).toRingHom w=0 ↔
        (z-algebraMap K U u)*(w-algebraMap K U v)=algebraMap K U b) := by
  let a := (f.coeff 1).coeff 1
  let c := (f.coeff 0).coeff 1
  let d := (f.coeff 1).coeff 0
  let e := (f.coeff 0).coeff 0
  have hex := expansion f hw.le hz.le
  change f=C (C a*X+C d)*X+C (C c*X+C e) at hex
  have hev (z w : U) : f.eval₂ (aeval z).toRingHom w=
      (algebraMap K U a*z+algebraMap K U d)*w+
        (algebraMap K U c*z+algebraMap K U e) := by
    rw [hex]
    simp only [eval₂_add,eval₂_mul,eval₂_C,eval₂_X,AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom,map_add,map_mul,aeval_C,aeval_X,a,c,d,e]
  by_cases ha : a=0
  · have hd : d ≠ 0 := by
      intro hd
      have hh : f.coeff 1 ≠ 0 := by rw [← hw]; exact coeff_natDegree (p := f) ▸ leadingCoeff_ne_zero.mpr hf.ne_zero
      apply hh
      have h := eq_X_add_C_of_natDegree_le_one
        ((BivariateDegree.coeff_natDegree_le_swap f 1).trans hz.le)
      change f.coeff 1=C a*X+C d at h
      simpa only [ha,hd,map_zero,zero_mul,add_zero] using h
    have hc : c ≠ 0 := by
      intro hc
      have hs : Bivariate.swap f=C (C d*X+C e) := by
        rw [hex]
        simp only [ha,hc,map_zero,zero_mul,zero_add,map_add,map_mul]
        simp [Bivariate.swap_C, Bivariate.swap_Y]
      rw [hs,natDegree_C] at hz
      omega
    left
    refine ⟨-c/d,-e/d,div_ne_zero (neg_ne_zero.mpr hc) hd,?_⟩
    intro z w
    have hd' : algebraMap K U d ≠ 0 := (_root_.map_ne_zero _).mpr hd
    rw [hev]
    simp only [ha,map_zero,zero_mul,zero_add,map_div₀,map_neg]
    constructor <;> intro h
    · field_simp
      linear_combination h
    · rw [h]
      field_simp
      ring
  · right
    have hb : (d*c-a*e)/a^2 ≠ 0 := by
      apply div_ne_zero _ (pow_ne_zero _ ha)
      intro h
      apply determinant_ne_zero f hf hw.le hz.le ha
      change a*e=c*d
      linear_combination -sub_eq_zero.mp h
    refine ⟨-d/a,-c/a,(d*c-a*e)/a^2,hb,?_⟩
    intro z w
    have ha' : algebraMap K U a ≠ 0 := (_root_.map_ne_zero _).mpr ha
    rw [hev]
    simp only [map_neg,map_div₀,map_sub,map_mul,map_pow]
    constructor <;> intro h
    · field_simp
      linear_combination h * algebraMap K U a
    · field_simp at h
      apply mul_left_cancel₀ ha'
      linear_combination h
end PlanarUnitDistances.BiAffine

namespace PlanarUnitDistances.CurveSeparation
open Polynomial
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma resultant_ne_zero (g f : B[X][X]) (hg : Irreducible g)
    (hd : g.natDegree ≠ 0) (hgf : ¬ g ∣ f) : g.resultant f ≠ 0 := by
  let φ := algebraMap B[X] (RatFunc B)
  have hi : Irreducible (g.map φ) :=
    (hg.isPrimitive hd).irreducible_iff_irreducible_map_fraction_map.mp hg
  have hnd : ¬ g.map φ ∣ f.map φ := by
    intro hh
    exact hgf ((hg.isPrimitive hd).dvd_iff_fraction_map_dvd_fraction_map (RatFunc B) |>.mpr hh)
  have hr := Polynomial.resultant_ne_zero (g.map φ) (f.map φ)
    (hi.coprime_iff_not_dvd.mpr hnd)
  have hm (p : B[X][X]) : (p.map φ).natDegree=p.natDegree :=
    natDegree_map_eq_of_injective (IsFractionRing.injective B[X] (RatFunc B)) p
  rw [hm g,hm f,resultant_map_map] at hr
  intro hz
  apply hr
  rw [hz,map_zero]

theorem eval_ne_zero (g f : B[X][X]) (hg : Irreducible g)
    (hd : g.natDegree ≠ 0) (hgf : ¬ g ∣ f) (a b : K)
    (ha : Transcendental B a) (hgroot : g.eval₂ (aeval a).toRingHom b=0) :
    f.eval₂ (aeval a).toRingHom b≠0 := by
  intro hfroot
  obtain ⟨p,q,_,_,he⟩ := exists_mul_add_mul_eq_C_resultant g f le_rfl le_rfl (Or.inl hd)
  have hh := congrArg (fun h : B[X][X] => h.eval₂ (aeval a).toRingHom b) he
  simp only [eval₂_add,eval₂_mul,eval₂_C] at hh
  rw [hgroot,hfroot,zero_mul,zero_mul,zero_add] at hh
  have hz : aeval a (g.resultant f)=0 := hh.symm
  exact (resultant_ne_zero g f hg hd hgf)
    (transcendental_iff_injective.mp ha (hz.trans (map_zero _).symm))

end PlanarUnitDistances.CurveSeparation

namespace PlanarUnitDistances.BivariateMaps
open Polynomial
variable {B K L : Type*} [Field B] [Field K] [Field L]
  [Algebra B K] [Algebra B L] [Algebra K L] [IsScalarTower B K L]

lemma eval_transport (f : B[X][X]) (a b : K) :
    algebraMap K L (f.eval₂ (aeval a).toRingHom b)=
      f.eval₂ (aeval (algebraMap K L a)).toRingHom (algebraMap K L b) := by
  induction f using Polynomial.induction_on' with
  | add f g hf hg => simp only [eval₂_add,map_add,hf,hg]
  | monomial n p =>
    simp only [eval₂_monomial,map_mul,map_pow]
    congr 1
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial m c =>
      simp [aeval_monomial,IsScalarTower.algebraMap_apply B K L]
end PlanarUnitDistances.BivariateMaps

namespace PlanarUnitDistances.Radicals
open Polynomial BivariateMaps
universe u
variable {k B K L : Type u} [Field k] [Field B] [CharZero B] [Field K] [CharZero K]
  [Field L] [Algebra k L] [Algebra B K] [Algebra K L] [IsAlgClosed K]
  [Algebra B L] [IsScalarTower B K L]

theorem curve_locus_differential_obstruction (D : Derivation k L L)
    (f g : B[X][X]) (hfK : Irreducible (bimap (algebraMap B K) f))
    (hfdeg : f.natDegree≠0) (hfsym : (Bivariate.swap f).natDegree=f.natDegree)
    (hgK : Irreducible (bimap (algebraMap B K) g))
    (hgdeg : g.natDegree≠0) (hgswap : (Bivariate.swap g).natDegree≠0)
    (hunit : g ∣ f → ∀ u v : B, ∃ z' w' : L, f.eval₂ (aeval z').toRingHom w'=0 ∧
      (z'-algebraMap B L u)*(w'-algebraMap B L v)≠1)
    (z w : L) (hz : Transcendental K z)
    (hroot : f.eval₂ (aeval z).toRingHom w=0)
    (a b da db t : Fin 4 → K) (ha : AlgebraicIndependent B a)
    (hb : ∀ i, g.eval₂ (aeval (a i)).toRingHom (b i)=0)
    (l : Fin 4 → L) (A : L) (hl : ∀ i, l i≠0)
    (hdist : ∀ i, (z-algebraMap K L (a i))*(w-algebraMap K L (b i))=2-l i-(l i)⁻¹)
    (hda : ∀ i, D (algebraMap K L (a i))=algebraMap K L (da i))
    (hdb : ∀ i, D (algebraMap K L (b i))=algebraMap K L (db i))
    (hlog : ∀ i, D (l i)/l i=A-algebraMap K L (t i))
    (hD : ∀ i, D (l i)≠0) : False := by
  have hf := irreducible_of_bimap (algebraMap B K) hfK
  have hg := irreducible_of_bimap (algebraMap B K) hgK
  have hrootK : (bimap (algebraMap B K) f).eval₂ (aeval z).toRingHom w=0 := by
    rwa [eval_bimap]
  by_cases hgf : g ∣ f
  · by_cases hdegree : 2≤f.natDegree
    · exact curve_curve_differential_obstruction D f g hfK hfdeg hgK hgswap z w hz
        hrootK a b da db t ha hb (fun _ => Or.inr hdegree) l A hl hdist hda hdb hlog hD
    have hf1 : f.natDegree=1 := by omega
    have hfs1 : (Bivariate.swap f).natDegree=1 := hfsym.trans hf1
    have hbf (i) : f.eval₂ (aeval (a i)).toRingHom (b i)=0 := by
      obtain ⟨q,rfl⟩ := hgf
      rw [eval₂_mul,hb,zero_mul]
    have hbfL (i) : f.eval₂ (aeval (algebraMap K L (a i))).toRingHom
        (algebraMap K L (b i))=0 := by
      rw [← eval_transport,hbf,map_zero]
    rcases BiAffine.line_or_circle (U := L) f hf hf1 hfs1 with he|hc
    · obtain ⟨e,e',he,heq⟩ := he
      have hw : w=algebraMap K L (algebraMap B K e)*z+algebraMap K L (algebraMap B K e') := by
        simpa only [← IsScalarTower.algebraMap_apply B K L] using (heq z w).mp hroot
      have hbr (i) : b i=algebraMap B K e*a i+algebraMap B K e' := by
        apply (algebraMap K L).injective
        simpa only [map_add,map_mul,← IsScalarTower.algebraMap_apply B K L]
          using (heq _ _).mp (hbfL i)
      exact line_differential_obstruction D e e' he z w hz hw a b da db t ha hbr
        l A hl hdist hda hdb hlog hD
    · obtain ⟨u,v,c,hc,heq⟩ := hc
      have hc1 : c≠1 := by
        intro h
        obtain ⟨z',w',hr,hu⟩ := hunit hgf u v
        apply hu
        simpa only [h,map_one] using (heq z' w').mp hr
      have hw : (z-algebraMap K L (algebraMap B K u))*
          (w-algebraMap K L (algebraMap B K v))=algebraMap K L (algebraMap B K c) := by
        simpa only [← IsScalarTower.algebraMap_apply B K L] using (heq z w).mp hroot
      have hbr (i) : (a i-algebraMap B K u)*(b i-algebraMap B K v)=algebraMap B K c := by
        apply (algebraMap K L).injective
        simpa only [map_mul,map_sub,← IsScalarTower.algebraMap_apply B K L]
          using (heq _ _).mp (hbfL i)
      exact circle_differential_obstruction D u v c hc hc1 z w hz hw a b da db t ha hbr
        l A hl hdist hda hdb hlog hD
  · exact curve_curve_differential_obstruction D f g hfK hfdeg hgK hgswap z w hz
      hrootK a b da db t ha hb
      (fun i => Or.inl (CurveSeparation.eval_ne_zero g f hg hgdeg hgf (a i) (b i)
        (ha.transcendental i) (hb i))) l A hl hdist hda hdb hlog hD
end PlanarUnitDistances.Radicals

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
open Polynomial BivariateMaps CoefficientField
universe u
variable {k B U : Type u} [Field k] [CharZero k] [Field B] [CharZero B]
  [Field U] [IsAlgClosed U] [Algebra k U] [Algebra B U]

theorem curve_curve (f g : B[X][X])
    (hfU : Irreducible (bimap (algebraMap B U) f)) (hfdeg : f.natDegree≠0)
    (hfsym : (Bivariate.swap f).natDegree=f.natDegree)
    (hgU : Irreducible (bimap (algebraMap B U) g))
    (hgdeg : g.natDegree≠0) (hgswap : (Bivariate.swap g).natDegree≠0)
    (z w : Fin 21 → U) (hz : AlgebraicIndependent B z)
    (hroot : ∀ i, f.eval₂ (aeval (z i)).toRingHom (w i)=0)
    (hunit : g ∣ f → ∀ u v : B, ∃ i, (z i-algebraMap B U u)*(w i-algebraMap B U v)≠1)
    (a b : Fin 4 → U) (ha : AlgebraicIndependent B a)
    (hb : ∀ j, g.eval₂ (aeval (a j)).toRingHom (b j)=0)
    (l : Fin 21 → Fin 4 → U) (htrans : ∀ i j, Transcendental k (l i j))
    (hrect : ∀ i j, ∃ c : k, l i j*l 0 0=l i 0*l 0 j*algebraMap k U c)
    (hdist : ∀ i j, (z i-a j)*(w i-b j)=2-l i j-(l i j)⁻¹) : False := by
  obtain ⟨D,A,t,hD,hlog⟩ := GridDerivation.exists_derivation_log l htrans hrect
  let y := parameters D a b t
  let K := FieldOf (B := B) y
  let : IsAlgClosed K := IsAlgClosure.isAlgClosed (IntermediateField.adjoin B (Set.range y))
  let : IsScalarTower B K U := IsScalarTower.of_algebraMap_eq fun _ => rfl
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
  have hai : AlgebraicIndependent B a' :=
    AlgebraicIndependent.of_comp (IsScalarTower.toAlgHom B K U) (by
      change AlgebraicIndependent B (fun j => algebraMap K U (a' j))
      simpa only [ha'] using ha)
  have hbb (j) : g.eval₂ (aeval (a' j)).toRingHom (b' j)=0 := by
    apply (algebraMap K U).injective
    rw [eval_transport,ha',hb',map_zero]
    exact hb j
  have hzz : AlgebraicIndependent B (fun iq : Fin 21 × Fin 1 => z iq.1) :=
    hz.comp Prod.fst (by intro ⟨i,q⟩ ⟨j,r⟩ h; exact Prod.ext h (Subsingleton.elim _ _))
  obtain ⟨i,hi⟩ := exists_left_block _ hzz y
  have hi' : Transcendental K (z i) := hi.transcendental 0
  have hfK : Irreducible (bimap (algebraMap B K) f) := by
    apply irreducible_of_bimap (algebraMap K U)
    rw [bimap_comp,← IsScalarTower.algebraMap_eq B K U]
    exact hfU
  have hgK : Irreducible (bimap (algebraMap B K) g) := by
    apply irreducible_of_bimap (algebraMap K U)
    rw [bimap_comp,← IsScalarTower.algebraMap_eq B K U]
    exact hgU
  apply Radicals.curve_locus_differential_obstruction D f g hfK hfdeg hfsym hgK
    hgdeg hgswap ?_ (z i) (w i) hi' (hroot i) a' b' da' db' t' hai hbb
    (l i) (A i) ?_ ?_ ?_ ?_ ?_ (hD i)
  · intro hgf u v
    obtain ⟨j,hj⟩ := hunit hgf u v
    exact ⟨z j,w j,hroot j,hj⟩
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

namespace PlanarUnitDistances.UltraPolynomial
open Polynomial Filter
open UnitDistances.UltraField

lemma polynomial_map_zero_iff {R S ι : Type*} {K : ι → Type*}
    [CommRing R] [CommRing S] [∀ i, CommRing (K i)]
    (F : Filter ι) (φ : R →+* S) (ψ : ∀ i,R →+* K i)
    (h : ∀ r, φ r=0 ↔ ∀ᶠ i in F, ψ i r=0) (p : R[X]) :
    p.map φ=0 ↔ ∀ᶠ i in F,p.map (ψ i)=0 := by
  classical
  constructor
  · intro hz
    have hc (j : ℕ) : ∀ᶠ i in F,ψ i (p.coeff j)=0 := by
      apply (h _).mp
      simpa only [coeff_map,coeff_zero] using congrArg (fun p : S[X] => p.coeff j) hz
    filter_upwards [(eventually_all_finset p.support).mpr (fun j _ => hc j)] with i hi
    ext j
    rw [coeff_map,coeff_zero]
    by_cases hj : j ∈ p.support
    · exact hi j hj
    · rw [notMem_support_iff.mp hj,map_zero]
  · intro hz
    ext j
    rw [coeff_map,coeff_zero,h]
    filter_upwards [hz] with i hi
    simpa only [coeff_map,coeff_zero] using congrArg (fun p : (K i)[X] => p.coeff j) hi

variable {ι : Type*} (U : Ultrafilter ι) (K : ι → Type*) [∀ i,Field (K i)]

lemma bimap_zero_iff (p : (∀ i,K i)[X][X]) :
    bimapping (mk U K) p=0 ↔ ∀ᶠ i in U,bimapping (Pi.evalRingHom K i) p=0 := by
  apply polynomial_map_zero_iff (U : Filter ι) (Polynomial.mapRingHom (mk U K))
    (fun i => Polynomial.mapRingHom (Pi.evalRingHom K i))
  intro q
  exact polynomial_map_zero_iff (U : Filter ι) (mk U K) (Pi.evalRingHom K)
    (fun r => by simpa only [Pi.evalRingHom_apply] using mk_eq_zero U K r) q

lemma bimap_eq_iff (p q : (∀ i,K i)[X][X]) :
    bimapping (mk U K) p=bimapping (mk U K) q ↔
      ∀ᶠ i in U,bimapping (Pi.evalRingHom K i) p=bimapping (Pi.evalRingHom K i) q := by
  simpa only [map_sub,sub_eq_zero] using bimap_zero_iff U K (p-q)

lemma bivariate_isUnit_iff {F : Type*} [Field F] (p : F[X][X]) :
    IsUnit p ↔ p=C (C ((p.coeff 0).coeff 0)) ∧ (p.coeff 0).coeff 0 ≠ 0 := by
  constructor
  · intro hp
    obtain ⟨q,hq,rfl⟩ := Polynomial.isUnit_iff.mp hp
    obtain ⟨c,hc,rfl⟩ := Polynomial.isUnit_iff.mp hq
    simp only [coeff_C_zero, true_and]
    exact hc.ne_zero
  · rintro ⟨he,hn⟩
    rw [he]
    exact isUnit_C.mpr (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hn))

lemma bimap_unit_iff (p : (∀ i,K i)[X][X]) :
    IsUnit (bimapping (mk U K) p) ↔ ∀ᶠ i in U,IsUnit (bimapping (Pi.evalRingHom K i) p) := by
  simp_rw [bivariate_isUnit_iff]
  have he := bimap_eq_iff U K p (C (C ((p.coeff 0).coeff 0)))
  have hn : mk U K ((p.coeff 0).coeff 0) ≠ 0 ↔
      ∀ᶠ i in U, (p.coeff 0).coeff 0 i ≠ 0 := by
    rw [ne_eq,mk_eq_zero,Ultrafilter.eventually_not]
  simpa only [bimapping,coe_mapRingHom,map_C,coeff_map,Pi.evalRingHom_apply,
    ← eventually_and] using he.and hn

lemma bimap_surjective : Function.Surjective (bimapping (mk U K)) :=
  Polynomial.map_surjective _ (Polynomial.map_surjective _ Ideal.Quotient.mk_surjective)

theorem irreducible_of_eventually (p : (∀ i,K i)[X][X])
    (hp : ∀ᶠ i in U,Irreducible (bimapping (Pi.evalRingHom K i) p)) :
    Irreducible (bimapping (mk U K) p) := by
  refine ⟨?_,?_⟩
  · intro hu
    have hev := (bimap_unit_iff U K p).mp hu
    obtain ⟨i,hi,hi'⟩ := (hp.and hev).exists
    exact hi.not_isUnit hi'
  · intro g h hmul
    obtain ⟨g',rfl⟩ := bimap_surjective U K g
    obtain ⟨h',rfl⟩ := bimap_surjective U K h
    have he := (bimap_eq_iff U K p (g'*h')).mp (by simpa only [map_mul] using hmul)
    have hu : ∀ᶠ i in U, IsUnit (bimapping (Pi.evalRingHom K i) g') ∨
        IsUnit (bimapping (Pi.evalRingHom K i) h') := by
      filter_upwards [hp,he] with i hi he
      exact hi.isUnit_or_isUnit (by simpa only [map_mul] using he)
    rcases Ultrafilter.eventually_or.mp hu with hg|hh
    · exact Or.inl ((bimap_unit_iff U K g').mpr hg)
    · exact Or.inr ((bimap_unit_iff U K h').mpr hh)

lemma pack_eval (f : ∀ i,(K i)[X][X]) (D : ℕ) (i : ι)
    (hf : (f i).natDegree ≤ D) (hc : ∀ m,((f i).coeff m).natDegree ≤ D) :
    bimapping (Pi.evalRingHom K i) (pack K f D)=f i := by
  simp only [pack,bimapping,coe_mapRingHom,map_sum,map_monomial]
  rw [as_sum_range' (f i) (D+1) (by omega)]
  apply Finset.sum_congr rfl
  intro m _
  simp only [Pi.evalRingHom_apply, ← map_sum]
  congr 1
  exact (as_sum_range' ((f i).coeff m) (D+1) (by have := hc m; omega)).symm

end PlanarUnitDistances.UltraPolynomial

namespace PlanarUnitDistances.UltraPolynomial
open Polynomial Filter
open UnitDistances.UltraField
variable {ι R S : Type*} {K : ι → Type*} [CommRing R] [CommRing S]
  [∀ i, CommRing (K i)]

lemma eventually_natDegree_map (U : Ultrafilter ι) (φ : R →+* S)
    (ψ : ∀ i, R →+* K i)
    (h : ∀ r, φ r=0 ↔ ∀ᶠ i in U, ψ i r=0) (p : R[X]) :
    ∀ᶠ i in U, (p.map (ψ i)).natDegree=(p.map φ).natDegree := by
  have hc (m : ℕ) : ∀ᶠ i in U, ψ i (p.coeff m)=0 ↔ φ (p.coeff m)=0 := by
    by_cases hz : φ (p.coeff m)=0
    · filter_upwards [(h _).mp hz] with i hi
      exact iff_of_true hi hz
    · have hn := Ultrafilter.eventually_not.mpr ((h _).not.mp hz)
      filter_upwards [hn] with i hi
      exact iff_of_false hi hz
  filter_upwards [(eventually_all_finset (Finset.range (p.natDegree+1))).mpr
    (fun m _ => hc m)] with i hi
  have hh (m : ℕ) : (p.map (ψ i)).coeff m=0 ↔ (p.map φ).coeff m=0 := by
    simp only [coeff_map]
    by_cases hm : m≤p.natDegree
    · exact hi m (Finset.mem_range.mpr (by omega))
    · simp only [coeff_eq_zero_of_natDegree_lt (not_le.mp hm),map_zero]
  apply Nat.le_antisymm
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    exact (hh m).mpr (coeff_eq_zero_of_natDegree_lt hm)
  · apply natDegree_le_iff_coeff_eq_zero.mpr
    intro m hm
    exact (hh m).mp (coeff_eq_zero_of_natDegree_lt hm)

variable (U : Ultrafilter ι) (F : ι → Type*) [∀ i, Field (F i)]
lemma eventually_outer_degree (p : (∀ i,F i)[X][X]) :
    ∀ᶠ i in U, (bimapping (Pi.evalRingHom F i) p).natDegree=
      (bimapping (mk U F) p).natDegree := by
  apply eventually_natDegree_map U (Polynomial.mapRingHom (mk U F))
    (fun i => Polynomial.mapRingHom (Pi.evalRingHom F i))
  intro p
  exact polynomial_map_zero_iff (U : Filter ι) (mk U F) (Pi.evalRingHom F)
    (fun r => mk_eq_zero U F r) p

end PlanarUnitDistances.UltraPolynomial

namespace PlanarUnitDistances.CountableCoefficients
open Polynomial
variable {U : Type*} [Field U]

lemma coeff_mem_left (f g : U[X][X]) (m n : ℕ) :
    (f.coeff m).coeff n ∈ field f g :=
  Subfield.subset_closure (Or.inl ⟨(m,n),rfl⟩)

lemma coeff_mem_right (f g : U[X][X]) (m n : ℕ) :
    (g.coeff m).coeff n ∈ field f g :=
  Subfield.subset_closure (Or.inr ⟨(m,n),rfl⟩)

lemma descend_map (B : Subfield U) (f : U[X][X])
    (h : ∀ m n, (f.coeff m).coeff n ∈ B) :
    (descend B f h).map (Polynomial.mapRingHom B.subtype)=f := by
  classical
  simp only [descend,Polynomial.map_sum,Polynomial.map_monomial,coe_mapRingHom,Subfield.subtype_apply]
  change (∑ m ∈ f.support, monomial m ((f.coeff m).sum fun n c => monomial n c))=f
  simp only [sum_monomial_eq]
  exact f.sum_monomial_eq

end PlanarUnitDistances.CountableCoefficients

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

lemma eval_swap (f : K[X][X]) (a b : K) :
    (Bivariate.swap f).eval₂ (evalRingHom a) b=f.eval₂ (evalRingHom b) a := by
  simpa only [coe_aevalAeval_eq_evalEval,eval₂_evalRingHom] using
    Bivariate.aevalAeval_swap (R := K) a b f

lemma zeros_swap (S : Finset α) (z w : α → K) (f : K[X][X]) :
    zeros S w z (Bivariate.swap f)=zeros S z w f := by
  simp only [zeros,eval_swap]

lemma size_swap (f : K[X][X]) : BivariateDegree.size (Bivariate.swap f)=BivariateDegree.size f := by
  simp only [BivariateDegree.size,Bivariate.swap_swap_apply,add_comm]

lemma zeros_card_le_of_degree_zero (S : Finset α) (z w : α → K)
    (hz : Set.InjOn z S) (f : K[X][X]) (hf : f ≠ 0) (hd : f.natDegree=0) :
    (zeros S z w f).card ≤ BivariateDegree.size f := by
  classical
  obtain ⟨p,hp⟩ := natDegree_eq_zero.mp hd
  subst f
  have hp0 : p ≠ 0 := fun h => hf (by simp [h])
  have hinj : Set.InjOn z (zeros S z w (C p)) := fun _ hx _ hy he =>
    hz (zeros_subset _ _ _ _ hx) (zeros_subset _ _ _ _ hy) he
  calc
    (zeros S z w (C p)).card = ((zeros S z w (C p)).image z).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ p.natDegree := by
      apply card_le_degree_of_subset_roots
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      apply (mem_roots hp0).mpr
      simpa only [eval₂_C,coe_evalRingHom,IsRoot.def] using
        (Finset.mem_filter.mp hx).2
    _ ≤ BivariateDegree.size (C p) := by
      simp only [BivariateDegree.size,natDegree_C,Bivariate.swap_C,
        natDegree_map_eq_of_injective C_injective,zero_add,le_refl]

lemma both_degrees_pos_of_many_zeros (S : Finset α) (z w : α → K)
    (hz : Set.InjOn z S) (hw : Set.InjOn w S) (f : K[X][X])
    (hf : f ≠ 0) (hc : BivariateDegree.size f < (zeros S z w f).card) :
    0<f.natDegree ∧ 0<(Bivariate.swap f).natDegree := by
  constructor
  · by_contra h
    exact (not_le_of_gt hc) (zeros_card_le_of_degree_zero S z w hz f hf (by omega))
  · by_contra h
    have hs0 : Bivariate.swap f ≠ 0 := fun he =>
      hf (Bivariate.swap.injective (he.trans (map_zero _).symm))
    have hh := zeros_card_le_of_degree_zero S w z hw (Bivariate.swap f) hs0 (by omega)
    rw [zeros_swap,size_swap] at hh
    exact (not_le_of_gt hc) hh

theorem eventually_both_degrees_pos (U : Ultrafilter ι) (t : ι → ℝ)
    (ht : Tendsto t (U : Filter ι) atTop) (S : ι → Finset α) (z w : α → K)
    (hz : ∀ i,Set.InjOn z (S i)) (hw : ∀ i,Set.InjOn w (S i))
    (f : ι → K[X][X]) (D : ℕ)
    (hf : ∀ᶠ i in U,f i ≠ 0 ∧ BivariateDegree.size (f i) ≤ D)
    (hc : Lower (U : Filter ι) t (fun i => ((zeros (S i) z w (f i)).card : ℝ)) 1) :
    ∀ᶠ i in U,0<(f i).natDegree ∧ 0<(Bivariate.swap (f i)).natDegree := by
  have hh := (hc.tendsto_atTop ht zero_lt_one).eventually_gt_atTop (D : ℝ)
  filter_upwards [hf,hh] with i hi hcount
  apply both_degrees_pos_of_many_zeros (S i) z w (hz i) (hw i) (f i) hi.1
  exact hi.2.trans_lt (Nat.cast_lt.mp hcount)

end PlanarUnitDistances.LocusAvoidance

namespace PlanarUnitDistances.PlaneIntersection
open Polynomial

variable {K : Type*} [Field K]

lemma resultant_ne_zero_of_irreducible (f g : K[X][X])
    (hf : Irreducible f) (hd : f.natDegree ≠ 0) (hfg : ¬ f ∣ g) :
    f.resultant g ≠ 0 := by
  let φ := algebraMap K[X] (RatFunc K)
  have hi : Irreducible (f.map φ) :=
    (hf.isPrimitive hd).irreducible_iff_irreducible_map_fraction_map.mp hf
  have hnd : ¬ f.map φ ∣ g.map φ := by
    intro hh
    exact hfg ((hf.isPrimitive hd).dvd_iff_fraction_map_dvd_fraction_map (RatFunc K) |>.mpr hh)
  have hr := Polynomial.resultant_ne_zero (f.map φ) (g.map φ)
    (hi.coprime_iff_not_dvd.mpr hnd)
  have hm (p : K[X][X]) : (p.map φ).natDegree=p.natDegree :=
    natDegree_map_eq_of_injective (IsFractionRing.injective K[X] (RatFunc K)) p
  rw [hm f,hm g,resultant_map_map] at hr
  intro hz
  apply hr
  rw [hz,map_zero]

lemma eval_resultant_zero (f g : K[X][X]) (a b : K)
    (hf : f.eval₂ (evalRingHom a) b=0) (hg : g.eval₂ (evalRingHom a) b=0)
    (hd : f.natDegree ≠ 0 ∨ g.natDegree ≠ 0) :
    (f.resultant g).eval a=0 := by
  obtain ⟨p,q,_,_,he⟩ := exists_mul_add_mul_eq_C_resultant f g le_rfl le_rfl hd
  have hh := congrArg (fun h : K[X][X] => h.eval₂ (evalRingHom a) b) he
  simpa only [eval₂_add,eval₂_mul,eval₂_C,hf,hg,zero_mul,zero_add,coe_evalRingHom] using hh.symm

lemma natDegree_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K[X]) {D : ℕ} (hA : ∀ i j, (A i j).natDegree ≤ D) :
    A.det.natDegree ≤ Fintype.card ι * D := by
  rw [Matrix.det_apply]
  apply natDegree_sum_le_of_forall_le
  intro g _
  have hs : (Equiv.Perm.sign g • ∏ i, A (g i) i).natDegree =
      (∏ i, A (g i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign g) with h|h
    · rw [h,one_smul]
    · rw [h,Units.neg_smul,one_smul,natDegree_neg]
  rw [hs]
  exact (natDegree_prod_le _ _).trans (by
    calc
      ∑ i, (A (g i) i).natDegree ≤ ∑ _i : ι,D := Finset.sum_le_sum (fun i _ => hA _ _)
      _ = _ := by simp)

lemma natDegree_resultant_le (f g : K[X][X]) {D : ℕ}
    (hf : ∀ i, (f.coeff i).natDegree ≤ D)
    (hg : ∀ i, (g.coeff i).natDegree ≤ D) :
    (f.resultant g).natDegree ≤ (f.natDegree+g.natDegree)*D := by
  unfold resultant
  apply (natDegree_det_le _ (D := D) ?_).trans_eq (by simp)
  intro i j
  induction j using Fin.addCases <;>
    simp only [sylvester,Matrix.of_apply,Fin.addCases_left,Fin.addCases_right]
  · split_ifs <;> simp_all only [natDegree_zero,Nat.zero_le]
  · split_ifs <;> simp_all only [natDegree_zero,Nat.zero_le]

theorem intersection_card_le {α : Type*} (S : Finset α) (z w : α → K)
    (hz : Set.InjOn z S) (f g : K[X][X]) (hf : Irreducible f)
    (hd : f.natDegree ≠ 0) (hfg : ¬ f ∣ g) {D : ℕ}
    (hfD : ∀ i, (f.coeff i).natDegree ≤ D)
    (hgD : ∀ i, (g.coeff i).natDegree ≤ D)
    (hSf : ∀ a ∈ S, f.eval₂ (evalRingHom (z a)) (w a)=0)
    (hSg : ∀ a ∈ S, g.eval₂ (evalRingHom (z a)) (w a)=0) :
    S.card ≤ (f.natDegree+g.natDegree)*D := by
  classical
  have hres := resultant_ne_zero_of_irreducible f g hf hd hfg
  calc
    S.card = (S.image z).card := (Finset.card_image_of_injOn hz).symm
    _ ≤ (f.resultant g).natDegree := by
      apply card_le_degree_of_subset_roots
      intro a ha
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ha
      exact (mem_roots hres).mpr (eval_resultant_zero f g (z x) (w x) (hSf x hx) (hSg x hx) (Or.inl hd))
    _ ≤ _ := natDegree_resultant_le f g hfD hgD

end PlanarUnitDistances.PlaneIntersection

namespace PlanarUnitDistances.RealCurveSymmetry
open Polynomial Filter LocusAvoidance PowerGrowth
attribute [local instance] Classical.propDecidable

lemma coeff_degree_le_swap_degree {K : Type*} [Field K] (f : K[X][X]) (m : ℕ) :
    (f.coeff m).natDegree ≤ (Bivariate.swap f).natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  rw [← BivariateDegree.coeff_swap f n m,coeff_eq_zero_of_natDegree_lt hn,coeff_zero]

lemma degree_le_size {K : Type*} [Field K] (f : K[X][X]) : f.natDegree ≤ BivariateDegree.size f :=
  Nat.le_add_right _ _

lemma coeff_degree_le_size {K : Type*} [Field K] (f : K[X][X]) (m : ℕ) :
    (f.coeff m).natDegree ≤ BivariateDegree.size f :=
  (coeff_degree_le_swap_degree f m).trans (Nat.le_add_left _ _)

lemma conjugate_injective : Function.Injective conjugate :=
  Polynomial.map_injective _ (Polynomial.map_injective _ star_injective)

lemma conjugate_degree (f : ℂ[X][X]) : (conjugate f).natDegree=f.natDegree :=
  natDegree_map_eq_of_injective (Polynomial.map_injective _ star_injective) f

lemma swap_conjugate (f : ℂ[X][X]) : Bivariate.swap (conjugate f)=conjugate (Bivariate.swap f) := by
  ext m n
  simp only [conjugate,BivariateDegree.coeff_swap,coeff_map,coe_mapRingHom]

lemma reflect_size (f : ℂ[X][X]) : BivariateDegree.size (reflect f)=BivariateDegree.size f := by
  unfold reflect BivariateDegree.size
  rw [Bivariate.swap_swap_apply,swap_conjugate,conjugate_degree,conjugate_degree]
  exact Nat.add_comm _ _

lemma reflect_degree (f : ℂ[X][X]) : (reflect f).natDegree=(Bivariate.swap f).natDegree := by
  rw [reflect,swap_conjugate,conjugate_degree]

lemma reflect_ne_zero {f : ℂ[X][X]} (hf : f ≠ 0) : reflect f ≠ 0 := by
  intro h
  have hh : conjugate f=0 := Bivariate.swap.injective (h.trans (map_zero _).symm)
  exact hf (conjugate_injective (hh.trans (by simp [conjugate])))

lemma reflect_eval (f : ℂ[X][X]) (z : ℂ) :
    (reflect f).eval₂ (evalRingHom z) (star z)=star (f.eval₂ (evalRingHom z) (star z)) := by
  rw [reflect,eval_swap]
  simpa only [conjugate,eval₂_evalRingHom,starRingEnd_apply,star_star] using
    map_mapRingHom_evalEval (starRingEnd ℂ) f z (star z)

theorem reflect_eq_const_mul {α : Type*} (S : Finset α) (z w : α → ℂ)
    (hz : Set.InjOn z S) (hw : ∀ p ∈ S,w p=star (z p))
    (f : ℂ[X][X]) (hf : Irreducible f) (hd : f.natDegree ≠ 0)
    {D : ℕ} (hD : BivariateDegree.size f ≤ D) (hcard : 2*D^2<S.card)
    (hzero : ∀ p ∈ S,f.eval₂ (evalRingHom (z p)) (w p)=0) :
    ∃ c : ℂ,c ≠ 0 ∧ reflect f=f*C (C c) := by
  have hdiv : f ∣ reflect f := by
    by_contra hn
    have hres := PlaneIntersection.intersection_card_le S z w hz f (reflect f) hf hd hn
      (fun m => (coeff_degree_le_size f m).trans hD)
      (fun m => (coeff_degree_le_size (reflect f) m).trans ((reflect_size f).le.trans hD))
      hzero (fun p hp => by rw [hw p hp,reflect_eval,← hw p hp,hzero p hp,star_zero])
    have hfD := (degree_le_size f).trans hD
    have hrD := (degree_le_size (reflect f)).trans ((reflect_size f).le.trans hD)
    have hb : (f.natDegree+(reflect f).natDegree)*D ≤ 2*D^2 := by
      nlinarith
    exact (not_le_of_gt hcard) (hres.trans hb)
  obtain ⟨g,hg⟩ := hdiv
  have hg0 : g ≠ 0 := right_ne_zero_of_mul (hg ▸ reflect_ne_zero hf.ne_zero)
  have hsize : BivariateDegree.size g=0 := by
    have he := BivariateDegree.size_mul hf.ne_zero hg0
    rw [← hg,reflect_size] at he
    omega
  obtain ⟨c,hc⟩ := (BivariateDegree.size_eq_zero_iff g).mp hsize
  refine ⟨c,?_,?_⟩
  · intro hc0
    exact hg0 (by rw [hc,hc0,map_zero,map_zero])
  · rw [hg,hc]

lemma projection_degrees_eq {f : ℂ[X][X]} (hf : f ≠ 0)
    {c : ℂ} (hc : c ≠ 0) (he : reflect f=f*C (C c)) :
    f.natDegree=(Bivariate.swap f).natDegree := by
  have h := congrArg Polynomial.natDegree he
  have hC : (C (C c) : ℂ[X][X]) ≠ 0 := by simpa using hc
  rw [reflect_degree,natDegree_mul hf hC,natDegree_C,Nat.add_zero] at h
  exact h.symm

end PlanarUnitDistances.RealCurveSymmetry

namespace PlanarUnitDistances.UltraCurve
open Polynomial Filter UnitDistances.UltraField UltraPolynomial
variable {ι : Type*} (U : Ultrafilter ι)

lemma eval_mk (p : (ι → ℂ)[X][X]) (z w : ι → ℂ) :
    (bimapping (mk U (fun _ => ℂ)) p).eval₂
      (evalRingHom (mk U (fun _ => ℂ) z)) (mk U (fun _ => ℂ) w)=
    mk U (fun _ => ℂ) (fun i => (bimapping (Pi.evalRingHom (fun _ => ℂ) i) p).eval₂
      (evalRingHom (z i)) (w i)) := by
  simp only [eval₂_evalRingHom,bimapping,coe_mapRingHom,map_mapRingHom_evalEval]
  congr 1
  funext i
  exact (map_mapRingHom_evalEval (Pi.evalRingHom (fun _ : ι => ℂ) i) p z w).symm

lemma swap_bimapping {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : R[X][X]) : Bivariate.swap (bimapping φ p)=bimapping φ (Bivariate.swap p) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add,hp,hq]
  | monomial n p =>
    induction p using Polynomial.induction_on' with
    | add p q hp hq => simp only [map_add,hp,hq]
    | monomial m c => simp only [bimapping,coe_mapRingHom,map_monomial,
        Bivariate.swap_monomial_monomial]

lemma pack_eq (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, BivariateDegree.size (f i)≤D) (i : ι) :
    bimapping (Pi.evalRingHom (fun _ => ℂ) i) (pack (fun _ => ℂ) f D)=f i :=
  pack_eval _ f D i ((RealCurveSymmetry.degree_le_size _).trans (hf i))
    (fun m => (RealCurveSymmetry.coeff_degree_le_size _ m).trans (hf i))

lemma locus_irreducible (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, Irreducible (f i) ∧ BivariateDegree.size (f i)≤D) :
    Irreducible (locus U f D) := by
  apply irreducible_of_eventually
  exact Eventually.of_forall fun i => by rw [pack_eq f D (fun i => (hf i).2)]; exact (hf i).1

lemma locus_root (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, BivariateDegree.size (f i)≤D) (p : ι → ℂ)
    (hp : ∀ᶠ i in U,(f i).eval₂ (evalRingHom (p i)) (star (p i))=0) :
    (locus U f D).eval₂ (evalRingHom (mk U (fun _ => ℂ) p))
      (mk U (fun _ => ℂ) (fun i => star (p i)))=0 := by
  rw [locus,eval_mk,mk_eq_zero]
  simpa only [pack_eq f D hf] using hp

lemma locus_degrees (t : ι → ℝ) (ht : Tendsto t (U : Filter ι) atTop)
    (S : ι → Finset ℂ) (hS : PowerGrowth.Lower (U : Filter ι) t (fun i => (S i).card) 1)
    (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i, Irreducible (f i) ∧ BivariateDegree.size (f i)≤D)
    (hz : ∀ᶠ i in U,∀ p∈S i,(f i).eval₂ (evalRingHom p) (star p)=0) :
    (locus U f D).natDegree≠0 ∧
    (Bivariate.swap (locus U f D)).natDegree=(locus U f D).natDegree := by
  have hzero : ∀ᶠ i in U,LocusAvoidance.zeros (S i) id star (f i)=S i := by
    filter_upwards [hz] with i hi
    exact Finset.filter_eq_self.mpr hi
  have hcount := (hS.congr (Eventually.mono hzero fun i hi => congrArg (fun s : Finset ℂ => (s.card : ℝ)) hi.symm))
  have hp := LocusAvoidance.eventually_both_degrees_pos U t ht S id star
    (fun _ => fun _ _ _ _ h => h) (fun _ => fun _ _ _ _ h => star_injective h) f D
    (Eventually.of_forall fun i => ⟨(hf i).1.ne_zero,(hf i).2⟩) hcount
  have hc := (hS.tendsto_atTop ht zero_lt_one).eventually_gt_atTop ((2*D^2 : ℕ) : ℝ)
  have hsym : ∀ᶠ i in U,(Bivariate.swap (f i)).natDegree=(f i).natDegree := by
    filter_upwards [hz,hp,hc] with i hi hpi hci
    obtain ⟨c,hcn,he⟩ := RealCurveSymmetry.reflect_eq_const_mul (S i) id star
      (fun _ _ _ _ h => h) (fun _ _ => rfl) (f i) (hf i).1 (by omega) (hf i).2
      (Nat.cast_lt.mp hci) hi
    exact (RealCurveSymmetry.projection_degrees_eq (hf i).1.ne_zero hcn he).symm
  have hdeg := eventually_outer_degree U (fun _ => ℂ) (pack (fun _ => ℂ) f D)
  have hswap := eventually_outer_degree U (fun _ => ℂ) (Bivariate.swap (pack (fun _ => ℂ) f D))
  simp only [← swap_bimapping,pack_eq f D (fun i => (hf i).2)] at hdeg hswap
  obtain ⟨i,hpi,hsi,hdi,hswi⟩ := (hp.and (hsym.and (hdeg.and hswap))).exists
  change (locus U f D).natDegree≠0 ∧ _
  change (f i).natDegree=(locus U f D).natDegree at hdi
  change (Bivariate.swap (f i)).natDegree=(Bivariate.swap (locus U f D)).natDegree at hswi
  constructor
  · omega
  · exact hswi.symm.trans (hsi.trans hdi)

end PlanarUnitDistances.UltraCurve

namespace PlanarUnitDistances.CirclePolynomial
open Polynomial
variable {B K : Type*} [Field B] [Field K] [Algebra B K]

lemma circle_ne_zero (u v : B) : circle u v≠0 := by
  intro h
  have hh := congrArg (fun p : B[X][X] => (p.coeff 1).coeff 1) h
  simp [circle,sub_mul,coeff_one] at hh

lemma circle_degree (u v : B) : (circle u v).natDegree=1 := by
  apply Nat.le_antisymm
  · apply (natDegree_sub_le _ _).trans
    apply max_le _ (by simp)
    apply natDegree_mul_le.trans
    have h1 : (C X-C (C u) : B[X][X]).natDegree=0 := by rw [← C_sub]; simp
    have h2 : (X-C (C v) : B[X][X]).natDegree=1 := natDegree_X_sub_C _
    rw [h1,h2]
  · apply le_natDegree_of_ne_zero
    intro h
    have hh := congrArg (fun p : B[X] => p.coeff 1) h
    simp [circle,sub_mul,coeff_one] at hh

lemma swap_circle (u v : B) : Bivariate.swap (circle u v)=circle v u := by
  simp only [circle,map_sub,map_mul,map_one,Bivariate.swap_X,Bivariate.swap_Y,
    Bivariate.swap_C_C]
  ring

lemma circle_size (u v : B) : BivariateDegree.size (circle u v)=2 := by
  simp only [BivariateDegree.size,swap_circle,circle_degree]

theorem eq_mul_const (f : B[X][X]) (hf : Irreducible f)
    (hd : f.natDegree≠0) (hs : (Bivariate.swap f).natDegree≠0)
    (u v : B) (z w : K) (hz : Transcendental B z)
    (hfroot : f.eval₂ (aeval z).toRingHom w=0)
    (hcircle : (z-algebraMap B K u)*(w-algebraMap B K v)=1) :
    ∃ c : B,c≠0 ∧ circle u v=f*C (C c) := by
  have hc : f ∣ circle u v := by
    by_contra hn
    exact CurveSeparation.eval_ne_zero f (circle u v) hf hd hn z w hz hfroot
      (by rw [eval_circle,hcircle,sub_self])
  obtain ⟨q,hq⟩ := hc
  have hq0 : q≠0 := right_ne_zero_of_mul (hq ▸ circle_ne_zero u v)
  have hsize : BivariateDegree.size q=0 := by
    have hh := BivariateDegree.size_mul hf.ne_zero hq0
    rw [← hq,circle_size] at hh
    have hfn : 2≤BivariateDegree.size f := by unfold BivariateDegree.size; omega
    omega
  obtain ⟨c,hc⟩ := (BivariateDegree.size_eq_zero_iff q).mp hsize
  refine ⟨c,?_,?_⟩
  · intro h
    exact hq0 (by rw [hc,h,map_zero,map_zero])
  · rw [hq,hc]
end PlanarUnitDistances.CirclePolynomial

namespace PlanarUnitDistances.ComplexCircle
open Polynomial

theorem centers_conjugate (S : Finset ℂ) (u v : ℂ) (hS : 2<S.card)
    (hroot : ∀ z ∈ S, (z-u)*(star z-v)=1) : v=star u := by
  classical
  by_contra hne
  let A := star v-u
  let B := v-star u
  let C := star u*star v-u*v
  let p : ℂ[X] := Polynomial.C B*X^2+Polynomial.C (C-A*v-u*B)*X+
    Polynomial.C (-u*(C-A*v)-A)
  have hp : p≠0 := by
    intro h
    have hh := congrArg (fun q : ℂ[X] => q.coeff 2) h
    have hb : B=0 := by simpa [p] using hh
    exact hne (sub_eq_zero.mp hb)
  have hd : p.natDegree≤2 := by
    apply (natDegree_add_le _ _).trans
    apply max_le _ (by simp only [natDegree_C]; omega)
    apply (natDegree_add_le _ _).trans
    apply max_le
    · exact (natDegree_mul_le).trans (by simp only [natDegree_C,natDegree_X_pow,Nat.zero_add]; omega)
    · exact (natDegree_mul_le).trans (by simp only [natDegree_C,natDegree_X,Nat.zero_add]; omega)
  have hz (z : ℂ) (hz : z∈S) : p.eval z=0 := by
    have hh := hroot z hz
    have hs := congrArg star hh
    simp only [star_mul,star_sub,star_star,star_one] at hs
    have hl : A*star z=B*z+C := by
      dsimp only [A,B,C]
      linear_combination hh-hs
    simp only [p,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    linear_combination A*hh-(z-u)*hl
  apply hp
  exact eq_zero_of_natDegree_lt_card_of_eval_eq_zero' p S hz (hd.trans_lt hS)

end PlanarUnitDistances.ComplexCircle

namespace PlanarUnitDistances.UltraCircle
open Polynomial Filter UnitDistances.UltraField UltraPolynomial UltraCurve CirclePolynomial
variable {ι : Type*} (U : Ultrafilter ι)

lemma eventual_equation (f : ι → ℂ[X][X]) (D : ℕ)
    (hf : ∀ i,BivariateDegree.size (f i)≤D) (u v c : ι → ℂ)
    (he : circle (mk U (fun _ => ℂ) u) (mk U (fun _ => ℂ) v)=
      locus U f D*C (C (mk U (fun _ => ℂ) c))) :
    ∀ᶠ i in U,circle (u i) (v i)=f i*C (C (c i)) := by
  let q : (ι → ℂ)[X][X] := (C X-C (C u))*(X-C (C v))-1
  have h : bimapping (mk U (fun _ => ℂ)) q=
      bimapping (mk U (fun _ => ℂ)) (pack (fun _ => ℂ) f D*C (C c)) := by
    simpa only [q,bimapping,coe_mapRingHom,Polynomial.map_sub,Polynomial.map_mul,
      Polynomial.map_C,Polynomial.map_X,Polynomial.map_one,circle,locus] using he
  have hh := (bimap_eq_iff U (fun _ => ℂ) q _).mp h
  filter_upwards [hh] with i hi
  simpa only [q,circle,map_mul,pack_eq f D hf,bimapping,coe_mapRingHom,
    Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_X,
    Polynomial.map_one,Pi.evalRingHom_apply] using hi

lemma mk_circle_iff (z u v : ι → ℂ) :
    (mk U (fun _ => ℂ) z-mk U (fun _ => ℂ) u)*
      (mk U (fun _ => ℂ) (fun i => star (z i))-mk U (fun _ => ℂ) v)=1 ↔
    ∀ᶠ i in U,(z i-u i)*(star (z i)-v i)=1 := by
  rw [← map_sub,← map_sub,← map_mul,← (mk U (fun _ => ℂ)).map_one,mk_eq_mk]
  rfl

lemma real_circle_iff (z u : ℂ) : (z-u)*(star z-star u)=1 ↔ ‖z-u‖=1 := by
  rw [← star_sub]
  change (z-u)*(starRingEnd ℂ) (z-u)=1 ↔ ‖z-u‖=1
  rw [Complex.mul_conj]
  constructor
  · intro h
    have hh : Complex.normSq (z-u)=1 := by exact_mod_cast h
    rw [Complex.normSq_eq_norm_sq] at hh
    nlinarith [norm_nonneg (z-u)]
  · intro h
    rw [Complex.normSq_eq_norm_sq,h]
    norm_num

theorem forbidden (t : ι → ℝ) (ht : Tendsto t (U : Filter ι) atTop)
    (S P : ι → Finset ℂ) (hsub : ∀ i,S i⊆P i)
    (hS : PowerGrowth.Lower (U : Filter ι) t (fun i => (S i).card) 1)
    (f : ι → ℂ[X][X]) (D : ℕ) (hf : ∀ i,BivariateDegree.size (f i)≤D)
    (hz : ∀ᶠ i in U,∀ z∈S i,(f i).eval₂ (evalRingHom z) (star z)=0)
    (p r u v c : ι → ℂ)
    (he : circle (mk U (fun _ => ℂ) u) (mk U (fun _ => ℂ) v)=
      locus U f D*C (C (mk U (fun _ => ℂ) c)))
    (hp : (mk U (fun _ => ℂ) p-mk U (fun _ => ℂ) u)*
      (mk U (fun _ => ℂ) (fun i => star (p i))-mk U (fun _ => ℂ) v)=1)
    (hr : (mk U (fun _ => ℂ) r-mk U (fun _ => ℂ) u)*
      (mk U (fun _ => ℂ) (fun i => star (r i))-mk U (fun _ => ℂ) v)=1)
    (hno : ∀ᶠ i in U,∀ a : ℂ,
      t i^((9:ℝ)/10)≤((P i).filter (fun z => ‖z-a‖=1)).card →
      ¬(‖p i-a‖=1 ∧ ‖r i-a‖=1)) : False := by
  classical
  have hc := (hS.tendsto_atTop ht zero_lt_one).eventually_gt_atTop (2 : ℝ)
  have hfull := hS (1/10) (by norm_num)
  obtain ⟨i,hei,hzi,hci,hfi,hpi,hri,hni⟩ :=
    ((eventual_equation U f D hf u v c he).and
      (hz.and (hc.and (hfull.and ((mk_circle_iff U p u v).mp hp |>.and
        ((mk_circle_iff U r u v).mp hr |>.and hno)))))).exists
  have hroot (z : ℂ) (hz : z∈S i) : (z-u i)*(star z-v i)=1 := by
    have hh := congrArg (fun q : ℂ[X][X] => q.eval₂ (evalRingHom z) (star z)) hei
    simp only [circle,eval₂_sub,eval₂_mul,eval₂_C,coe_evalRingHom,eval_X,eval_C,
      eval₂_X,eval₂_one,hzi z hz,zero_mul] at hh
    exact sub_eq_zero.mp hh
  have hv := ComplexCircle.centers_conjugate (S i) (u i) (v i) (Nat.cast_lt.mp hci) hroot
  have hmem : S i⊆(P i).filter (fun z => ‖z-u i‖=1) := by
    intro z hzs
    refine Finset.mem_filter.mpr ⟨hsub i hzs,?_⟩
    apply (real_circle_iff z (u i)).mp
    rw [← hv]
    exact hroot z hzs
  apply hni (u i)
  · apply (show t i^((9:ℝ)/10)≤((S i).card : ℝ) by convert hfi using 1; norm_num).trans
    exact_mod_cast Finset.card_le_card hmem
  · constructor
    · exact (real_circle_iff _ _).mp (hv ▸ hpi)
    · exact (real_circle_iff _ _).mp (hv ▸ hri)
end PlanarUnitDistances.UltraCircle

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

namespace PlanarUnitDistances.LocusBlocks
open Filter PowerGrowth GenericGrid PolynomialBlocks UnitDistanceBlockAvoidance MvPolynomial
variable {ι α K : Type*} [Field K]

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

lemma single_independent {B : Type} [Field B] (U : Ultrafilter ℕ)
    [Algebra B (UltraCurve.CU U)] {m : ℕ} (p : Fin m → ℕ → ℂ)
    (h : AlgebraicIndependent B (fun iq : Fin m × Fin 1 => z U (p iq.1))) :
    AlgebraicIndependent B (fun i => z U (p i)) :=
  h.comp (fun i => (i,0)) (fun _ _ he => congrArg Prod.fst he)

lemma locus_root_descend {B : Type} [Field B] (U : Ultrafilter ℕ)
    [Algebra B (UltraCurve.CU U)] (f : ℕ → ℂ[X][X]) (D : ℕ)
    (hf : ∀ n,BivariateDegree.size (f n)≤D) (f' : B[X][X])
    (hmap : bimap (algebraMap B (UltraCurve.CU U)) f'=UltraCurve.locus U f D)
    (p : ℕ → ℂ) (hp : ∀ᶠ n in U,(f n).eval₂ (evalRingHom (p n)) (star (p n))=0) :
    f'.eval₂ (aeval (z U p)).toRingHom (w U p)=0 := by
  have hh := UltraCurve.locus_root U f D hf p hp
  rw [← hmap] at hh
  have hc : (evalRingHom (z U p)).comp
      (mapRingHom (algebraMap B (UltraCurve.CU U)))=(aeval (z U p)).toRingHom := by
    ext <;> simp
  rw [BivariateMaps.bimap,coe_mapRingHom,eval₂_map,hc] at hh
  exact hh

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

lemma map_circle {B L : Type*} [Field B] [Field L] (φ : B →+* L) (u v : B) :
    BivariateMaps.bimap φ (CirclePolynomial.circle u v)=CirclePolynomial.circle (φ u) (φ v) := by
  simp only [CirclePolynomial.circle,BivariateMaps.bimap,coe_mapRingHom,
    map_sub,map_mul,map_C,map_X,map_one]

variable (U : Ultrafilter ℕ) (hU : (U : Filter ℕ)≤atTop) (t J : ℕ → ℝ)
  (ht : Tendsto t (U : Filter ℕ) atTop) (hJ : Tendsto J (U : Filter ℕ) atTop)
  (P A B : ℕ → Finset ℂ) (E : ℕ → ℂ → ℂ → Prop)
  (hsub : ∀ n,A n⊆P n ∧ B n⊆P n)
  (hA : Upper (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hB : Upper (U : Filter ℕ) t (fun n => (B n).card) 1)
  (hAf : Lower (U : Filter ℕ) t (fun n => (A n).card) 1)
  (hBf : Lower (U : Filter ℕ) t (fun n => (B n).card) 1)
  (he : Lower (U : Filter ℕ) t
    (fun n => (GenericGrid.edges (fun n (a : A n) (b : B n) => E n a b) n).card) 2)
  (K : ℕ → Type) [∀ n,Field (K n)] [∀ n,NumberField (K n)] [∀ n,IsGalois ℚ (K n)]
  (e : ∀ n,K n →+* ℂ) (ell : ∀ n,ℂ → ℂ → K n)
  (H : Hypotheses U t J P E K e ell)

include hU ht hJ hsub hA hB hAf hBf he H
lemma curve_curve_oai (hcurveA : DenseLoci.OnCurve U A id star)
    (hcurveB : DenseLoci.OnCurve U B id star) : False := by
  let : Algebra (constants (K := K) hJ) (UltraCurve.CU U) :=
    UltraHeightGrid.complexAlgebra U K hJ e
  obtain ⟨D,f,hf,hfroots⟩ := hcurveA
  obtain ⟨Dg,g,hg,hgroots⟩ := hcurveB
  let fu := UltraCurve.locus U f D
  let gu := UltraCurve.locus U g Dg
  let L := CountableCoefficients.field fu gu
  let f' : L[X][X] := CountableCoefficients.descend L fu
    (CountableCoefficients.coeff_mem_left fu gu)
  let g' : L[X][X] := CountableCoefficients.descend L gu
    (CountableCoefficients.coeff_mem_right fu gu)
  have hfmap : BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f'=fu :=
    CountableCoefficients.descend_map L fu (CountableCoefficients.coeff_mem_left fu gu)
  have hgmap : BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) g'=gu :=
    CountableCoefficients.descend_map L gu (CountableCoefficients.coeff_mem_right fu gu)
  have hfI : Irreducible (BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f') := by
    rw [hfmap]; exact UltraCurve.locus_irreducible U f D hf
  have hgI : Irreducible (BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) g') := by
    rw [hgmap]; exact UltraCurve.locus_irreducible U g Dg hg
  have hfdU := UltraCurve.locus_degrees U t ht A hAf f D hf hfroots
  have hgdU := UltraCurve.locus_degrees U t ht B hBf g Dg hg hgroots
  have hfd : f'.natDegree≠0 ∧ (Bivariate.swap f').natDegree=f'.natDegree := by
    simpa only [← show BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) f'=
      UltraCurve.locus U f D from hfmap,bimap_swap,bimap_natDegree] using hfdU
  have hgd : g'.natDegree≠0 ∧ (Bivariate.swap g').natDegree=g'.natDegree := by
    simpa only [← show BivariateMaps.bimap (algebraMap L (UltraCurve.CU U)) g'=
      UltraCurve.locus U g Dg from hgmap,bimap_swap,bimap_natDegree] using hgdU
  obtain ⟨p,r,hgrid,hp,hr⟩ := GenericGrid.exists_real_grid U hU t ht A B E hA hB he
    (fun p : ℂ => fun _ : Fin 1 => p) (fun p : ℂ => fun _ : Fin 1 => p)
    (by intro s; rfl) (by intro s; rfl)
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (a : A n) => (a:ℂ))
      (fun _ => Subtype.val_injective))
    (LocusBlocks.curve_uniformBlocks (U : Filter ℕ) t ht (fun n (b : B n) => (b:ℂ))
      (fun _ => Subtype.val_injective)) 20 3 L
  have hgP : ∀ᶠ n in U,∀ i j,p i n∈P n ∧ r j n∈P n ∧ E n (p i n) (r j n) := by
    filter_upwards [hgrid] with n hn i j
    exact ⟨(hsub n).1 (hn i j).1,(hsub n).2 (hn i j).2.1,(hn i j).2.2⟩
  obtain ⟨htrans,hrect,hdist⟩ := grid_labels hJ (fun _ => rfl) H p r hgP
  have hp' : AlgebraicIndependent L (fun i => z U (p i)) := single_independent U p hp
  have hr' : AlgebraicIndependent L (fun j => z U (r j)) := single_independent U r hr
  have hp0 (i) : f'.eval₂ (aeval (z U (p i))).toRingHom (w U (p i))=0 := by
    apply locus_root_descend U f D (fun n => (hf n).2) f' hfmap (p i)
    filter_upwards [hgrid,hfroots] with n hn hrn
    exact hrn _ (hn i 0).1
  have hr0 (j) : g'.eval₂ (aeval (z U (r j))).toRingHom (w U (r j))=0 := by
    apply locus_root_descend U g Dg (fun n => (hg n).2) g' hgmap (r j)
    filter_upwards [hgrid,hgroots] with n hn hrn
    exact hrn _ (hn 0 j).2.1
  have hunit : g' ∣ f' → ∀ u v : L,∃ i,
      (z U (p i)-algebraMap L (UltraCurve.CU U) u)*
        (w U (p i)-algebraMap L (UltraCurve.CU U) v)≠1 := by
    intro hgf u v
    by_contra! hall
    obtain ⟨c,hc,heq⟩ := CirclePolynomial.eq_mul_const f'
      (irreducible_of_bimap (algebraMap L (UltraCurve.CU U)) hfI)
      hfd.1 (by rw [hfd.2]; exact hfd.1) u v (z U (p 0)) (w U (p 0))
      (hp'.transcendental 0) (hp0 0) (hall 0)
    have heqU : CirclePolynomial.circle (algebraMap L (UltraCurve.CU U) u)
        (algebraMap L (UltraCurve.CU U) v)=
        fu*C (C (algebraMap L (UltraCurve.CU U) c)) := by
      rw [← map_circle,heq,map_mul,hfmap]
      simp only [BivariateMaps.bimap,coe_mapRingHom,map_C]
    have hrf : f'.eval₂ (aeval (z U (r 0))).toRingHom (w U (r 0))=0 := by
      obtain ⟨q,hq⟩ := hgf
      rw [hq,eval₂_mul,hr0 0,zero_mul]
    have hrc : (z U (r 0)-algebraMap L (UltraCurve.CU U) u)*
        (w U (r 0)-algebraMap L (UltraCurve.CU U) v)=1 := by
      have hh := congrArg (fun q : L[X][X] => q.eval₂
        (aeval (z U (r 0))).toRingHom (w U (r 0))) heq
      rw [CirclePolynomial.eval_circle,eval₂_mul,hrf,zero_mul] at hh
      exact sub_eq_zero.mp hh
    obtain ⟨us,hu⟩ := Ideal.Quotient.mk_surjective (algebraMap L (UltraCurve.CU U) u)
    obtain ⟨vs,hv⟩ := Ideal.Quotient.mk_surjective (algebraMap L (UltraCurve.CU U) v)
    obtain ⟨cs,hcs⟩ := Ideal.Quotient.mk_surjective (algebraMap L (UltraCurve.CU U) c)
    apply UltraCircle.forbidden U t ht A P (fun n => (hsub n).1) hAf f D
      (fun n => (hf n).2) hfroots (p 0) (r 0) us vs cs
    · simpa only [hu,hv,hcs] using heqU
    · simpa only [hu,hv] using hall 0
    · simpa only [hu,hv] using hrc
    · filter_upwards [hgP] with n hn
      exact H.no_circle n _ (hn 0 0).1 _ (hn 0 0).2.1 (hn 0 0).2.2
  exact GridObstruction.curve_curve f' g' hfI hfd.1 hfd.2 hgI hgd.1
    (by rw [hgd.2]; exact hgd.1) (fun i => z U (p i)) (fun i => w U (p i)) hp' hp0 hunit
    (fun j => z U (r j)) (fun j => w U (r j)) hr' hr0
    (fun i j => EdgeLabels.label U K e ell (p i) (r j)) htrans hrect hdist
end PlanarUnitDistances.AlgebraicObstruction

end OAI
end

theorem solution : type_of% @OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve_oai := @OAI.PlanarUnitDistances.AlgebraicObstruction.curve_curve_oai
