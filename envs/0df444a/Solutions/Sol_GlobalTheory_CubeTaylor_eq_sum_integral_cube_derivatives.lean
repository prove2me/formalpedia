-- Prove2me | solution 1 for GlobalTheory.CubeTaylor.eq_sum_integral_cube_derivatives
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:02:40.52193+00:00
-- url     : https://prove2.me/submissions/64dd1de4-b902-49bf-b922-e879be69c8ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LocallyIntegrableRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_SobolevIteratedOneParameterSubgroups
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqSumIntegralCubeDerivatives
import Theorems.Thm_GlobalTheory_continuous_prod_ofFn_curves
import Theorems.Thm_GlobalTheory_integral_cube_succ_last

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MeasureTheory
open scoped ContDiff
namespace GlobalTheory.CubeTaylor
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
open MeasureTheory in
open scoped ContDiff in
private theorem integral_cube_succ_eq_iterated {K : Type} [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [CompleteSpace K] (N : ℕ) (s : ℝ) (F : (Fin (N + 1) → ℝ) → K)
    (hF : Continuous F) :
    ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t =
      ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
        ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) := by
  have hsnoc : Continuous fun p : (Fin N → ℝ) × ℝ => (Fin.snoc p.1 p.2 : Fin (N + 1) → ℝ) :=
    Continuous.finSnoc (A := fun _ => ℝ) continuous_fst continuous_snd
  have hF' : Continuous fun p : (Fin N → ℝ) × ℝ => F (Fin.snoc p.1 p.2) := hF.comp hsnoc
  have hG : Continuous fun t : Fin N → ℝ => ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) :=
    continuous_parametric_integral_of_continuous (f := fun t r => F (Fin.snoc t r)) hF'
      isCompact_Icc
  have hcube : IsCompact (Set.univ.pi fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hcube' : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  set X := ∫ t in Set.univ.pi (fun _ : Fin (N + 1) => Set.Icc (0 : ℝ) s), F t with hX
  set Y := ∫ t in Set.univ.pi (fun _ : Fin N => Set.Icc (0 : ℝ) s),
    ∫ r in Set.Icc (0 : ℝ) s, F (Fin.snoc t r) with hY
  have key : ∀ e : K, (inner ℂ e X).re = (inner ℂ e Y).re := by
    intro e
    let L : K →L[ℝ] ℝ := Complex.reCLM.comp ((innerSL ℂ e).restrictScalars ℝ)
    have hL : ∀ x, L x = (inner ℂ e x).re := fun x => rfl
    rw [← hL, ← hL, hX, hY,
      ← L.integral_comp_comm (hF.continuousOn.integrableOn_compact hcube),
      ← L.integral_comp_comm (hG.continuousOn.integrableOn_compact hcube'),
      (_root_.GlobalTheory.integral_cube_succ_last N s (fun t => L (F t)) (L.continuous.comp hF)).2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    exact L.integral_comp_comm
      ((hF.comp (Continuous.finSnoc (A := fun _ => ℝ) continuous_const continuous_id)).continuousOn.integrableOn_compact
        isCompact_Icc)
  have h := key (X - Y)
  have h2 : ‖X - Y‖ ^ 2 = 0 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ), inner_sub_right, map_sub]
    simp only [RCLike.re_to_complex]
    rw [h, sub_self]
  exact sub_eq_zero.1 (norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h2))
open MeasureTheory in
open scoped ContDiff in
private theorem eq_interval_average_sub_weighted_deriv
    {G : Type} [Group G] [TopologicalSpace G] {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ρ : G →* (K →L[ℂ] K)) (hcont : ∀ v, Continuous fun g => ρ g v)
    {s : ℝ} (hs : 0 < s) (c : ℝ → G) (hc : Continuous c) (hc0 : c 0 = 1)
    (hadd : ∀ a b, c (a + b) = c a * c b) (w w' : K)
    (hd : HasDerivAt (fun t : ℝ => ρ (c t) w) w' 0) :
    w = (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w) -
      ∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
  have hg : ∀ r, HasDerivAt (fun t => ρ (c t) w) (ρ (c r) w') r := by
    intro r
    have h1 : HasDerivAt (fun t => ρ (c (t - r)) w) w' r := by
      have := hd
      rw [← sub_self r] at this
      exact this.comp_sub_const r r
    have h2 := ((ρ (c r)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt r h1
    refine h2.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.coe_restrictScalars']
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← hadd, add_sub_cancel]
  have hb : ∀ r : ℝ, HasDerivAt (fun t : ℝ => (((s - t) / s : ℝ) : ℂ)) (((-(1 / s)) : ℝ) : ℂ) r := by
    intro r
    have : HasDerivAt (fun t : ℝ => (s - t) / s) (-(1 / s)) r := by
      simpa [neg_div] using ((hasDerivAt_id r).const_sub s).div_const s
    exact this.ofReal_comp
  have hh : ∀ r ∈ Set.uIcc 0 s, HasDerivAt (fun t => (((s - t) / s : ℝ) : ℂ) • ρ (c t) w)
      ((((s - r) / s : ℝ) : ℂ) • ρ (c r) w' + (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w) r :=
    fun r _ => (hb r).smul (hg r)
  have hgc : Continuous fun t => ρ (c t) w := (hcont w).comp hc
  have hg'c : Continuous fun t => ρ (c t) w' := (hcont w').comp hc
  have hA : Continuous fun r : ℝ => (((s - r) / s : ℝ) : ℂ) • ρ (c r) w' := by
    exact (Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul hg'c
  have hB : Continuous fun r : ℝ => (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w :=
    continuous_const.smul hgc
  have hE := intervalIntegral.integral_eq_sub_of_hasDerivAt hh
    ((hA.add hB).intervalIntegrable 0 s)
  rw [intervalIntegral.integral_add (hA.intervalIntegrable 0 s) (hB.intervalIntegrable 0 s),
    intervalIntegral.integral_of_le hs.le, intervalIntegral.integral_of_le hs.le] at hE
  simp only [sub_self, zero_div, Complex.ofReal_zero, zero_smul, sub_zero, div_self hs.ne',
    Complex.ofReal_one, one_smul, hc0, map_one, ContinuousLinearMap.one_apply] at hE
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc]
  have hneg : ∫ r in Set.Ioc 0 s, (((-(1 / s)) : ℝ) : ℂ) • ρ (c r) w =
      -∫ r in Set.Ioc 0 s, ((1 / s : ℝ) : ℂ) • ρ (c r) w := by
    rw [← integral_neg]
    congr 1
    funext r
    rw [Complex.ofReal_neg, neg_smul]
  rw [hneg] at hE
  have key : ∀ x A B : K, A + -B = 0 - x → x = B - A := by
    intro x A B h
    calc x = -(0 - x) := by abel
      _ = -(A + -B) := by rw [h]
      _ = B - A := by abel
  exact key _ _ _ hE
end GlobalTheory.CubeTaylor
end

set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
open GlobalTheory GlobalTheory.CubeTaylor
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
open MeasureTheory
open scoped ContDiff
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
namespace GlobalTheory.CubeTaylor
namespace _root_.GlobalTheory.CubeTaylor
theorem _root_.solution : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K], ∀ (ρ : G →* (K →L[ℂ] K)), (∀ g v, ‖ρ g v‖ = ‖v‖) → (∀ v, Continuous fun g => ρ g v) → ∀ (s : ℝ), 0 < s → ∀ (N : ℕ) (c : Fin N → ℝ → G), (∀ i, Continuous (c i) ∧ c i 0 = 1 ∧ ∀ a b, c i (a + b) = c i a * c i b) → ∃ (J : Type) (_ : Fintype J) (κ : J → (Fin N → ℝ) → ℂ) (l : J → List (Fin N)), (∀ j, Continuous (κ j)) ∧ ∀ (d : Fin N → K → K) (S : Set K), (∀ v ∈ S, ∀ i, d i v ∈ S ∧ HasDerivAt (fun t : ℝ => ρ (c i t) v) (d i v) 0) → ∀ v ∈ S, v = ∑ j, ∫ t in Set.pi Set.univ (fun _ : Fin N => Set.Icc (0 : ℝ) s), κ j t • ρ (List.ofFn fun i => c i (t i)).prod ((l j).foldr d v) := by
  intro G _ _ _ K _ _ _ ρ _ hcont s hs N
  induction N with
  | zero =>
    intro c hc
    refine ⟨Unit, inferInstance, fun _ _ => 1, fun _ => [], fun _ => continuous_const, ?_⟩
    intro d S hS v hv
    simp [Measure.real, Real.volume_Icc_pi]
  | succ N ih =>
    intro c hc
    obtain ⟨J, hJ, κ, l, hκ, hrep⟩ := ih (fun i => c (Fin.castSucc i)) (fun i => hc _)
    have hinit : Continuous (fun t : Fin (N + 1) → ℝ => Fin.init t) :=
      continuous_pi fun i => continuous_apply (Fin.castSucc i)
    refine ⟨J × Bool, inferInstance,
      fun p t => κ p.1 (Fin.init t) * (if p.2 then ((1 / s : ℝ) : ℂ)
        else -(((s - t (Fin.last N)) / s : ℝ) : ℂ)),
      fun p => if p.2 then (l p.1).map Fin.castSucc else Fin.last N :: (l p.1).map Fin.castSucc,
      ?_, ?_⟩
    · rintro ⟨j, _ | _⟩
      · simp only [Bool.false_eq_true, if_false]
        exact ((hκ j).comp hinit).mul (by fun_prop)
      · simp only [if_true]
        exact ((hκ j).comp hinit).mul continuous_const
    intro d S hS v hv
    have hS' : ∀ v ∈ S, ∀ i : Fin N, d (Fin.castSucc i) v ∈ S ∧
        HasDerivAt (fun t : ℝ => ρ (c (Fin.castSucc i) t) v) (d (Fin.castSucc i) v) 0 :=
      fun v hv i => hS v hv _
    have h1 := hrep (fun i => d (Fin.castSucc i)) S hS' v hv
    have hmem : ∀ l' : List (Fin N), l'.foldr (fun i => d (Fin.castSucc i)) v ∈ S := by
      intro l'
      induction l' with
      | nil => exact hv
      | cons a l' ihl => exact (hS _ ihl _).1
    have hfold : ∀ l' : List (Fin N),
        (l'.map Fin.castSucc).foldr d v = l'.foldr (fun i => d (Fin.castSucc i)) v := by
      intro l'
      rw [List.foldr_map]
    have hPc : ∀ x : K, Continuous fun t : Fin N → ℝ =>
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x := fun x =>
      (hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves N _ fun i => (hc _).1)
    have hcF : ∀ (f : (Fin (N + 1) → ℝ) → ℂ) (x : K), Continuous f →
        Continuous fun t => f t • ρ (List.ofFn fun i => c i (t i)).prod x := fun f x hf =>
      hf.smul ((hcont x).comp (_root_.GlobalTheory.continuous_prod_ofFn_curves _ c fun i => (hc i).1))
    have hprod : ∀ (t : Fin N → ℝ) (r : ℝ),
        (List.ofFn fun i => c i ((Fin.snoc t r : Fin (N + 1) → ℝ) i)).prod =
          (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod * c (Fin.last N) r := by
      intro t r
      rw [List.ofFn_succ', List.prod_concat]
      simp
    rw [Fintype.sum_prod_type]
    refine h1.trans (Finset.sum_congr rfl fun j _ => ?_)
    simp only [Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, List.foldr_cons, hfold]
    rw [integral_cube_succ_eq_iterated N s _ (hcF (fun t => κ j (Fin.init t) * ((1 / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul continuous_const)),
      integral_cube_succ_eq_iterated N s _
        (hcF (fun t => κ j (Fin.init t) * -(((s - t (Fin.last N)) / s : ℝ) : ℂ)) _
        (((hκ j).comp hinit).mul (by fun_prop)))]
    simp only [Fin.init_snoc, Fin.snoc_last, hprod, map_mul, ContinuousLinearMap.mul_apply]
    set u := (l j).foldr (fun i => d (Fin.castSucc i)) v with hu_def
    have hu : u ∈ S := hmem _
    set cl := c (Fin.last N) with hcl
    have hA := eq_interval_average_sub_weighted_deriv ρ hcont hs cl (hc _).1 (hc _).2.1
      (hc _).2.2 u (d (Fin.last N) u) (hS u hu _).2
    have hI1 : IntegrableOn (fun r => ((1 / s : ℝ) : ℂ) • ρ (cl r) u) (Set.Icc 0 s) :=
      (continuous_const.smul ((hcont u).comp (hc _).1)).continuousOn.integrableOn_compact
        isCompact_Icc
    have hI2 : IntegrableOn (fun r => (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))
        (Set.Icc 0 s) :=
      ((Complex.continuous_ofReal.comp ((continuous_const.sub continuous_id).div_const s)).smul
        ((hcont _).comp (hc _).1)).continuousOn.integrableOn_compact isCompact_Icc
    have e1 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * ((1 / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) u) =
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, ((1 / s : ℝ) : ℂ) • ρ (cl r) u) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI1, ← integral_smul]
      congr 1
      funext r
      rw [map_smul, smul_smul]
    have e2 : ∀ t : Fin N → ℝ, ∫ r in Set.Icc (0 : ℝ) s, (κ j t * -(((s - r) / s : ℝ) : ℂ)) •
        ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod (ρ (cl r) (d (Fin.last N) u)) =
        -(κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod
          (∫ r in Set.Icc 0 s, (((s - r) / s : ℝ) : ℂ) • ρ (cl r) (d (Fin.last N) u))) := by
      intro t
      rw [← ContinuousLinearMap.integral_comp_comm _ hI2, ← integral_smul, ← integral_neg]
      congr 1
      funext r
      rw [map_smul, smul_smul, mul_neg, neg_smul]
    simp only [e1, e2]
    have hcube : IsCompact (Set.univ.pi fun _ : Fin N => Set.Icc (0 : ℝ) s) :=
      isCompact_univ_pi fun _ => isCompact_Icc
    have hi : ∀ x : K, IntegrableOn (fun t : Fin N → ℝ =>
        κ j t • ρ (List.ofFn fun i => c (Fin.castSucc i) (t i)).prod x)
        (Set.univ.pi fun _ => Set.Icc (0 : ℝ) s) := fun x =>
      ((hκ j).smul (hPc x)).continuousOn.integrableOn_compact hcube
    rw [integral_neg, ← sub_eq_add_neg, ← integral_sub (hi _) (hi _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [← smul_sub, ← map_sub, ← hA]
end _root_.GlobalTheory.CubeTaylor
end GlobalTheory.CubeTaylor
