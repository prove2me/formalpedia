-- Prove2me | solution 1 for MuirheadMST.bartlett_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T20:20:25.76438+00:00
-- url     : https://prove2.me/submissions/2e37f8ec-a217-4462-9728-db7254c0d55e

import Mathlib
import Definitions.Def_MuirheadMST_Wishart

open MeasureTheory ProbabilityTheory WithLp

noncomputable section

namespace BartlettAux

open MuirheadMST

abbrev E (k : ℕ) := EuclideanSpace ℝ (Fin k)

/-- The law of `‖g‖` for `g` standard Gaussian in `ℝ^k`. -/
def chi (k : ℕ) : Measure ℝ := (stdGaussian (E k)).map (fun x => ‖x‖)

/-- Bartlett's upper-triangular factor from its diagonal `d` and the array `t`. -/
def T {m : ℕ} (d : Fin m → ℝ) (t : Fin m → Fin m → ℝ) (i j : Fin m) : ℝ :=
  if i = j then d i else if i < j then t i j else 0

/-- `TᵀT`. -/
def B {m : ℕ} (d : Fin m → ℝ) (t : Fin m → Fin m → ℝ) : Fin m → Fin m → ℝ :=
  fun j k => ∑ i, T d t i j * T d t i k

/-- Gram matrix of `m` column vectors in `ℝ^n`. -/
def gramC {m n : ℕ} (z : Fin m → E n) : Fin m → Fin m → ℝ := fun j k => inner ℝ (z j) (z k)

/-- Bartlett side, with the diagonal entries already replaced by their χ laws. -/
def BLaw (m n : ℕ) : Measure (Fin m → Fin m → ℝ) :=
  ((Measure.pi fun i : Fin m => chi (n - i)).prod
    (Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m => gaussianReal 0 1)).map
    (fun p => B p.1 p.2)

/-- Gaussian side: Gram matrix of `m` i.i.d. standard Gaussian columns in `ℝ^n`. -/
def GLaw (m n : ℕ) : Measure (Fin m → Fin m → ℝ) :=
  (Measure.pi fun _ : Fin m => stdGaussian (E n)).map gramC

/-- The block matrix `[[r², r aᵀ], [r a, a aᵀ + M]]`. -/
def H {m : ℕ} (r : ℝ) (a : Fin m → ℝ) (M : Fin m → Fin m → ℝ) : Fin (m + 1) → Fin (m + 1) → ℝ :=
  fun j k => Fin.cases (Fin.cases (r ^ 2) (fun k => r * a k) k)
    (fun j => Fin.cases (r * a j) (fun k => a j * a k + M j k) k) j

instance (k : ℕ) : SigmaFinite (stdGaussian (E k)) := IsFiniteMeasure.toSigmaFinite _

instance (k : ℕ) : IsProbabilityMeasure (chi k) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

lemma measurable_B {m : ℕ} : Measurable (fun p : (Fin m → ℝ) × (Fin m → Fin m → ℝ) => B p.1 p.2) := by
  refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => ?_
  refine Finset.measurable_sum _ fun i _ => ?_
  unfold T
  refine Measurable.mul ?_ ?_ <;> split_ifs <;> fun_prop

lemma measurable_gramC {m n : ℕ} : Measurable (gramC : (Fin m → E n) → _) := by
  unfold gramC
  fun_prop

lemma measurable_H {m : ℕ} :
    Measurable (fun p : ℝ × (Fin m → ℝ) × (Fin m → Fin m → ℝ) => H p.1 p.2.1 p.2.2) := by
  refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => ?_
  cases j using Fin.cases <;> cases k using Fin.cases <;>
    simp only [H, Fin.cases_zero, Fin.cases_succ] <;> fun_prop

instance (m n : ℕ) : IsProbabilityMeasure (BLaw m n) :=
  Measure.isProbabilityMeasure_map measurable_B.aemeasurable

instance (m n : ℕ) : IsProbabilityMeasure (GLaw m n) :=
  Measure.isProbabilityMeasure_map measurable_gramC.aemeasurable

/-- Two pushforwards of product measures agree when their fibres agree. -/
lemma map_prod_eq_of_fiber {X Y Y' Z : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Y'] [MeasurableSpace Z] (μ : Measure X) (ν : Measure Y) (ν' : Measure Y')
    [SFinite ν] [SFinite ν'] {f : X × Y → Z} {f' : X × Y' → Z} (hf : Measurable f)
    (hf' : Measurable f') (h : ∀ x, ν.map (fun y => f (x, y)) = ν'.map (fun y => f' (x, y))) :
    (μ.prod ν).map f = (μ.prod ν').map f' := by
  ext s hs
  rw [Measure.map_apply hf hs, Measure.map_apply hf' hs, Measure.prod_apply (hf hs),
    Measure.prod_apply (hf' hs)]
  refine lintegral_congr fun x => ?_
  have := congrArg (fun ρ : Measure Z => ρ s) (h x)
  rwa [Measure.map_apply (f := fun y => f (x, y)) (hf.comp measurable_prodMk_left) hs,
    Measure.map_apply (f := fun y => f' (x, y)) (hf'.comp measurable_prodMk_left) hs] at this

/-- Splitting off the first coordinate of a standard Gaussian vector. -/
def S {n : ℕ} (w : E (n + 1)) : ℝ × E n := (w.ofLp 0, toLp 2 (fun i => w.ofLp i.succ))

lemma S_mp (n : ℕ) :
    MeasurePreserving (S (n := n)) (stdGaussian (E (n + 1)))
      ((gaussianReal 0 1).prod (stdGaussian (E n))) := by
  have h1 := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gaussianReal 0 1) 0
  have h2 : MeasurePreserving (toLp 2) (Measure.pi fun _ : Fin n => gaussianReal 0 1)
      (stdGaussian (E n)) := ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have h3 : MeasurePreserving (toLp 2) (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1)
      (stdGaussian (E (n + 1))) := ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have h4 := (MeasurePreserving.id (gaussianReal 0 1)).prod h2 |>.comp h1
  have h5 : MeasurePreserving (ofLp) (stdGaussian (E (n + 1)))
      (Measure.pi fun _ : Fin (n + 1) => gaussianReal 0 1) := by
    refine ⟨by fun_prop, ?_⟩
    rw [← h3.map_eq, Measure.map_map (by fun_prop) (by fun_prop)]
    exact Measure.map_id
  convert h4.comp h5 using 1
  funext w
  simp [S, MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rfl

lemma inner_S {n : ℕ} (w v : E (n + 1)) :
    inner ℝ w v = (S w).1 * (S v).1 + inner ℝ (S w).2 (S v).2 := by
  simp only [S, PiLp.inner_apply, Fin.sum_univ_succ, RCLike.inner_apply, conj_trivial]
  ring

lemma rot_mp {m n : ℕ} (R : E n ≃ₗᵢ[ℝ] E n) :
    MeasurePreserving (fun (z : Fin m → E n) j => R (z j))
      (Measure.pi fun _ => stdGaussian (E n)) (Measure.pi fun _ => stdGaussian (E n)) :=
  measurePreserving_pi _ _ fun _ => ⟨R.continuous.measurable, stdGaussian_map R⟩

lemma exists_rot {n : ℕ} (z₀ : E (n + 1)) :
    ∃ R : E (n + 1) ≃ₗᵢ[ℝ] E (n + 1), ∀ w, inner ℝ z₀ (R w) = ‖z₀‖ * w.ofLp 0 := by
  set e : E (n + 1) := EuclideanSpace.single 0 ‖z₀‖
  have he : ‖z₀‖ = ‖e‖ := by simp [e]
  refine ⟨Submodule.reflection (ℝ ∙ (z₀ - e))ᗮ, fun w => ?_⟩
  rw [← (Submodule.reflection (ℝ ∙ (z₀ - e))ᗮ).inner_map_map, Submodule.reflection_reflection,
    Submodule.reflection_sub he]
  simp [e, EuclideanSpace.inner_single_left]

lemma fiber {m n : ℕ} (z₀ : E (n + 1)) :
    (Measure.pi fun _ : Fin m => stdGaussian (E (n + 1))).map
        (fun zr => gramC (Fin.cons z₀ zr : Fin (m + 1) → E (n + 1))) =
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (GLaw m n)).map
        (fun p => H ‖z₀‖ p.1 p.2) := by
  obtain ⟨R, hR⟩ := exists_rot z₀
  have h1 := measurePreserving_pi _ _ (fun _ : Fin m => S_mp n)
  have h2 := measurePreserving_arrowProdEquivProdArrow ℝ (E n) (Fin m)
    (fun _ => gaussianReal 0 1) (fun _ => stdGaussian (E n))
  have h3 : MeasurePreserving (Prod.map id gramC)
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin m => stdGaussian (E n)))
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (GLaw m n)) :=
    (MeasurePreserving.id _).prod ⟨measurable_gramC, rfl⟩
  have h := (h3.comp h2).comp h1
  rw [← (rot_mp (m := m) R).map_eq, Measure.map_map (by exact measurable_gramC.comp (by fun_prop))
    (rot_mp R).measurable, ← h.map_eq,
    Measure.map_map (g := fun p => H ‖z₀‖ p.1 p.2)
      (measurable_H.comp (measurable_const.prodMk measurable_id)) h.measurable]
  congr 1
  funext zr j k
  simp only [Function.comp_apply, Prod.map, id, MeasurableEquiv.arrowProdEquivProdArrow,
    MeasurableEquiv.coe_mk, Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_mk]
  cases j using Fin.cases <;> cases k using Fin.cases <;>
    simp only [H, gramC, Fin.cases_zero, Fin.cases_succ, Fin.cons_zero, Fin.cons_succ]
  · rw [real_inner_self_eq_norm_sq]
  · rw [hR]; rfl
  · rw [real_inner_comm, hR]; rfl
  · rw [LinearIsometryEquiv.inner_map_map, inner_S]

lemma GLaw_succ (m n : ℕ) :
    GLaw (m + 1) (n + 1) = ((chi (n + 1)).prod
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (GLaw m n))).map
        (fun p => H p.1 p.2.1 p.2.2) := by
  have hc := (measurePreserving_piFinSuccAbove
    (fun _ : Fin (m + 1) => stdGaussian (E (n + 1))) 0).symm
  have hcons : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => E (n + 1)) 0).symm =
      fun p => Fin.cons p.1 p.2 := by
    funext p
    simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rw [hcons] at hc
  have key : GLaw (m + 1) (n + 1) =
      ((stdGaussian (E (n + 1))).prod (Measure.pi fun _ : Fin m => stdGaussian (E (n + 1)))).map
        (fun p => gramC (Fin.cons p.1 p.2 : Fin (m + 1) → E (n + 1))) := by
    rw [GLaw, ← hc.map_eq, Measure.map_map measurable_gramC hc.measurable]
    rfl
  rw [key]
  have hf : Measurable (fun p : E (n + 1) × (Fin m → E (n + 1)) =>
      gramC (Fin.cons p.1 p.2 : Fin (m + 1) → E (n + 1))) :=
    measurable_gramC.comp hc.measurable
  rw [map_prod_eq_of_fiber _ _ ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (GLaw m n))
    hf (measurable_H.comp (measurable_norm.prodMap measurable_id)) (fun z₀ => fiber z₀)]
  unfold chi
  rw [← Measure.map_id (μ := (Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (GLaw m n)),
    Measure.map_prod_map _ _ measurable_norm measurable_id, Measure.map_id,
    Measure.map_map measurable_H (measurable_norm.prodMap measurable_id)]

lemma rearr {A B C D : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    [MeasurableSpace D] (μa : Measure A) (μb : Measure B) (μc : Measure C) (μd : Measure D)
    [SFinite μa] [SFinite μb] [SFinite μc] [SFinite μd] :
    MeasurePreserving (fun p : (A × B) × (C × D) => (p.1.1, (p.2.1, (p.1.2, p.2.2))))
      ((μa.prod μb).prod (μc.prod μd)) (μa.prod (μc.prod (μb.prod μd))) := by
  have h1 := measurePreserving_prodAssoc μa μb (μc.prod μd)
  have h2 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μb μc μd).symm
  have h3 := (MeasurePreserving.id μa).prod
    ((Measure.measurePreserving_swap (μ := μb) (ν := μc)).prod (MeasurePreserving.id μd))
  have h4 := (MeasurePreserving.id μa).prod (measurePreserving_prodAssoc μc μb μd)
  exact (h4.comp (h3.comp (h2.comp h1)))

lemma tail_mp (m : ℕ) :
    MeasurePreserving (fun (r : Fin (m + 1) → ℝ) (k : Fin m) => r k.succ)
      (Measure.pi fun _ => gaussianReal 0 1) (Measure.pi fun _ => gaussianReal 0 1) := by
  have h := (measurePreserving_snd (μ := gaussianReal 0 1)).comp
    (measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => gaussianReal 0 1) 0)
  convert h using 1
  funext r k
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]

lemma Φ1_mp (m n : ℕ) :
    MeasurePreserving (fun (d : Fin (m + 1) → ℝ) => (d 0, fun i : Fin m => d i.succ))
      (Measure.pi fun i : Fin (m + 1) => chi (n + 1 - i))
      ((chi (n + 1)).prod (Measure.pi fun i : Fin m => chi (n - i))) := by
  have h := measurePreserving_piFinSuccAbove (fun i : Fin (m + 1) => chi (n + 1 - i)) 0
  have e2 : (fun j : Fin m => chi (n + 1 - ((Fin.succAbove 0 j : Fin (m + 1)) : ℕ))) =
      fun j : Fin m => chi (n - (j : ℕ)) := by
    funext j
    simp
  simp only [Fin.val_zero, Nat.sub_zero, e2] at h
  convert h using 1
  funext d
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv]
  rfl

lemma Φ2_mp (m : ℕ) :
    MeasurePreserving
      (fun (t : Fin (m + 1) → Fin (m + 1) → ℝ) =>
        ((fun k : Fin m => t 0 k.succ), fun (i k : Fin m) => t i.succ k.succ))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      ((Measure.pi fun _ => gaussianReal 0 1).prod
        (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)) := by
  have h := ((tail_mp m).prod (measurePreserving_pi _ _ fun _ : Fin m => tail_mp m)).comp
    (measurePreserving_piFinSuccAbove
      (fun _ : Fin (m + 1) => Measure.pi fun _ : Fin (m + 1) => gaussianReal 0 1) 0)
  convert h using 1
  funext t
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.tail]

lemma B_succ {m : ℕ} (d : Fin (m + 1) → ℝ) (t : Fin (m + 1) → Fin (m + 1) → ℝ) :
    B d t = H (d 0) (fun k => t 0 k.succ) (B (fun i => d i.succ) (fun i k => t i.succ k.succ)) := by
  have h00 : T d t 0 0 = d 0 := by simp [T]
  have hs0 : ∀ i : Fin m, T d t i.succ 0 = 0 := fun i => by
    simp [T, Fin.succ_ne_zero, (Fin.succ_pos i).not_gt]
  have h0s : ∀ k : Fin m, T d t 0 k.succ = t 0 k.succ := fun k => by
    simp [T, (Fin.succ_ne_zero k).symm, Fin.succ_pos k]
  have hss : ∀ i k : Fin m, T d t i.succ k.succ =
      T (fun i => d i.succ) (fun i k => t i.succ k.succ) i k := fun i k => by
    simp [T, Fin.succ_inj, Fin.succ_lt_succ_iff]
  funext j k
  cases j using Fin.cases <;> cases k using Fin.cases <;>
    simp only [B, H, Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_succ, h00, hs0, h0s, hss,
      zero_mul, mul_zero, Finset.sum_const_zero, add_zero] <;> ring

lemma prod_map_right {X Y Z : Type*} [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace Z]
    (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν] {g : Y → Z} (hg : Measurable g) :
    μ.prod (ν.map g) = (μ.prod ν).map (Prod.map id g) := by
  rw [← Measure.map_prod_map _ _ measurable_id hg, Measure.map_id]

lemma BLaw_succ (m n : ℕ) :
    BLaw (m + 1) (n + 1) = ((chi (n + 1)).prod
      ((Measure.pi fun _ : Fin m => gaussianReal 0 1).prod (BLaw m n))).map
        (fun p => H p.1 p.2.1 p.2.2) := by
  have hΨ := (rearr _ _ _ _).comp ((Φ1_mp m n).prod (Φ2_mp m))
  rw [BLaw, BLaw, prod_map_right _ _ measurable_B, prod_map_right _ _ (measurable_id.prodMap measurable_B),
    Measure.map_map measurable_H (measurable_id.prodMap (measurable_id.prodMap measurable_B)),
    ← hΨ.map_eq, Measure.map_map
      (measurable_H.comp (measurable_id.prodMap (measurable_id.prodMap measurable_B)))
      hΨ.measurable]
  congr 1
  funext p
  exact B_succ p.1 p.2

lemma BLaw_eq_GLaw : ∀ m n, m ≤ n → BLaw m n = GLaw m n := by
  intro m
  induction m with
  | zero =>
    intro n _
    ext s hs
    rcases Set.eq_empty_or_nonempty s with rfl | ⟨x, hx⟩
    · simp
    · have : s = Set.univ := Set.eq_univ_of_forall fun y => Subsingleton.elim x y ▸ hx
      subst this
      simp
  | succ m ih =>
    intro n hmn
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [BLaw_succ, GLaw_succ, ih n (by omega)]

lemma bartlett_eq_BLaw (m n : ℕ) :
    (bartlettLaw m n).map (fun ω j k => ∑ i, bartlettFactor ω i j * bartlettFactor ω i k) =
      BLaw m n := by
  have hn : (Measure.pi fun i : Fin m => stdGaussian (E (n - i))).map (fun g i => ‖g i‖) =
      Measure.pi fun i : Fin m => chi (n - i) := by
    have : ∀ i : Fin m, SigmaFinite ((stdGaussian (E (n - i))).map (fun x => ‖x‖)) :=
      fun i => inferInstanceAs (SigmaFinite (chi (n - i)))
    exact Measure.pi_map_pi (fun i => measurable_norm.aemeasurable)
  have hm : Measurable (fun (g : ∀ i : Fin m, E (n - i)) i => ‖g i‖) :=
    measurable_pi_lambda _ fun i => (measurable_pi_apply i).norm
  rw [BLaw, ← hn, ← Measure.map_id (μ := Measure.pi fun _ : Fin m => Measure.pi fun _ : Fin m =>
      gaussianReal 0 1), Measure.map_prod_map _ _ hm measurable_id,
    Measure.map_map measurable_B (hm.prodMap measurable_id)]
  rfl

/-- Transposing an array of i.i.d. `N(0,1)` entries preserves its law. -/
lemma transpose_mp (m n : ℕ) :
    MeasurePreserving (fun (x : Fin n → Fin m → ℝ) j i => x i j)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1) := by
  have hm : Measurable (fun (x : Fin n → Fin m → ℝ) j i => x i j) := by fun_prop
  refine ⟨hm, (Measure.pi_eq_generateFrom (fun _ => generateFrom_pi) (fun _ => isPiSystem_pi)
    (fun _ => Measure.FiniteSpanningSetsIn.pi fun _ => (gaussianReal 0 1).toFiniteSpanningSetsIn)
    fun s hs => ?_).symm⟩
  choose u hu hus using hs
  have hs' : s = fun j => Set.pi Set.univ (u j) := funext fun j => (hus j).symm
  subst hs'
  have hu' : ∀ j i, MeasurableSet (u j i) := fun j i => hu j i (Set.mem_univ _)
  have hpre : (fun (x : Fin n → Fin m → ℝ) j i => x i j) ⁻¹'
      Set.pi Set.univ (fun j => Set.pi Set.univ (u j)) =
      Set.pi Set.univ (fun i => Set.pi Set.univ (fun j => u j i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_implies]
    exact forall_comm
  rw [Measure.map_apply hm (MeasurableSet.univ_pi fun j => MeasurableSet.univ_pi (hu' j)), hpre,
    Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact Finset.prod_comm

lemma wishart_eq_GLaw (m n : ℕ) : wishart m n 1 = GLaw m n := by
  have hA : ∀ k l : ℕ, MeasurePreserving (fun (x : Fin k → Fin l → ℝ) i => toLp 2 (x i))
      (Measure.pi fun _ => Measure.pi fun _ => gaussianReal 0 1)
      (Measure.pi fun _ => stdGaussian (E l)) := fun k l =>
    measurePreserving_pi _ _ fun _ => ⟨by fun_prop, map_pi_eq_stdGaussian⟩
  have hgram : ∀ x : Fin n → Fin m → ℝ,
      gram (fun i => toLp 2 (x i)) = gramC (fun j => toLp 2 (fun i => x i j)) := by
    intro x
    funext j k
    simp only [gram, gramC, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hgm : Measurable (gram : (Fin n → E m) → Fin m → Fin m → ℝ) := by
    unfold gram; fun_prop
  rw [wishart, normalDataMatrix, multivariateGaussian_zero_one, ← (hA n m).map_eq,
    Measure.map_map hgm (hA n m).measurable, GLaw, ← (hA m n).map_eq,
    ← (transpose_mp m n).map_eq, Measure.map_map (hA m n).measurable (transpose_mp m n).measurable,
    Measure.map_map measurable_gramC ((hA m n).measurable.comp (transpose_mp m n).measurable)]
  congr 1
  funext x
  exact hgram x

end BartlettAux

open BartlettAux in
theorem solution (m n : ℕ) (hmn : m ≤ n) :
    (MuirheadMST.bartlettLaw m n).map
        (fun ω j k => ∑ i, MuirheadMST.bartlettFactor ω i j * MuirheadMST.bartlettFactor ω i k) =
      MuirheadMST.wishart m n 1 := by
  rw [bartlett_eq_BLaw, wishart_eq_GLaw, BLaw_eq_GLaw m n hmn]
