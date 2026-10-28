-- Prove2me | solution 1 for NonsmoothLojasiewicz.Convex.prop29_moreauEnv_C1_subanalytic
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-28T07:10:23.983873+00:00
-- url     : https://prove2.me/submissions/5bd539e9-a6ff-449e-bae9-94779a739025

import Mathlib
import Definitions.Def_MoreauProx_Characterization_GammaZero
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Convex_moreauEnv
import Theorems.Thm_NonsmoothLojasiewicz_Convex_infDist_isSubanalyticFn
import Theorems.Thm_NonsmoothLojasiewicz_Convex_moreauEnv_properties

set_option autoImplicit false

open Filter Topology
open MoreauProx.Characterization

namespace Bdf5447aRed

open NonsmoothLojasiewicz.Continuous

/-- Drop coordinate `0` of a vector of `ℝ^(m+1)`. -/
noncomputable def tailL (m : ℕ) :
    EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v => WithLp.toLp 2 (fun i => v i.succ)
      map_add' := fun v w => by ext i; simp
      map_smul' := fun r v => by ext i; simp }

/-- Prepend a coordinate. -/
noncomputable def consE {m : ℕ} (w : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin (m + 1)) :=
  WithLp.toLp 2 (Fin.cons w (fun i => y i))

theorem tailL_apply {m : ℕ} (v : EuclideanSpace ℝ (Fin (m + 1))) (i : Fin m) :
    tailL m v i = v i.succ := rfl

theorem consE_zero {m : ℕ} (w : ℝ) (y : EuclideanSpace ℝ (Fin m)) : consE w y 0 = w := rfl

theorem consE_succ {m : ℕ} (w : ℝ) (y : EuclideanSpace ℝ (Fin m)) (i : Fin m) :
    consE w y i.succ = y i := rfl

theorem tailL_consE {m : ℕ} (w : ℝ) (y : EuclideanSpace ℝ (Fin m)) :
    tailL m (consE w y) = y := by
  ext i
  rw [tailL_apply, consE_succ]

theorem normsq_split {m : ℕ} (v : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖v‖ ^ 2 = (v 0) ^ 2 + ‖tailL m v‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    Real.sq_sqrt (by positivity), Fin.sum_univ_succ]
  simp [tailL_apply, Real.norm_eq_abs, sq_abs]

theorem norm_le_split {m : ℕ} (v : EuclideanSpace ℝ (Fin (m + 1))) :
    ‖v‖ ≤ |v 0| + ‖tailL m v‖ := by
  have h := normsq_split v
  have h0 := norm_nonneg v
  have h1 := norm_nonneg (tailL m v)
  have h2 := abs_nonneg (v 0)
  have h3 := sq_abs (v 0)
  nlinarith

/-- Embed `ℝⁿ` as the hyperplane `{v 0 = 0}` of `ℝ^(n+1)`. -/
noncomputable def embL (n : ℕ) :
    EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => consE 0 x
      map_add' := fun x y => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [consE]
        · simp [consE]
      map_smul' := fun r x => by
        ext i
        refine Fin.cases ?_ (fun j => ?_) i
        · simp [consE]
        · simp [consE] }

theorem embL_apply {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : embL n x = consE 0 x := rfl

theorem semi_basic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {F G : X → ℝ} (hF : ∀ x, AnalyticAt ℝ F x)
    (hG : ∀ x, AnalyticAt ℝ G x) :
    IsSemianalytic {x | F x = 0 ∧ 0 < G x} := by
  intro x₀
  refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, 1, fun _ _ => F, fun _ _ => G,
    fun _ _ => ⟨fun x _ => hF x, fun x _ => hG x⟩, ?_⟩
  ext x
  simp

theorem semi_preimage {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {Φ : X → Y} (hΦ : ∀ x, AnalyticAt ℝ Φ x) {B : Set Y} (hB : IsSemianalytic B) :
    IsSemianalytic (Φ ⁻¹' B) := by
  intro x₀
  obtain ⟨V, hVo, hxV, p, q, F, G, hFG, hEq⟩ := hB (Φ x₀)
  have hc : Continuous Φ := continuous_iff_continuousAt.2 fun x => (hΦ x).continuousAt
  refine ⟨Φ ⁻¹' V, hVo.preimage hc, hxV, p, q, fun i j y => F i j (Φ y),
    fun i j y => G i j (Φ y), ?_, ?_⟩
  · intro i j
    exact ⟨(hFG i j).1.comp (fun y _ => hΦ y) (fun y hy => hy),
      (hFG i j).2.comp (fun y _ => hΦ y) (fun y hy => hy)⟩
  · ext y
    have h := Set.ext_iff.mp hEq (Φ y)
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_iInter,
      Set.mem_setOf_eq] at h ⊢
    exact h

theorem semi_inter {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] {A A' : Set X} (hA : IsSemianalytic A) (hA' : IsSemianalytic A') :
    IsSemianalytic (A ∩ A') := by
  intro x₀
  obtain ⟨V, hVo, hxV, p, q, F, G, hFG, hEq⟩ := hA x₀
  obtain ⟨V', hVo', hxV', p', q', F', G', hFG', hEq'⟩ := hA' x₀
  let F'' : Fin (p * p') → Fin (q + q') → X → ℝ := fun i j =>
    Fin.addCases (motive := fun _ => X → ℝ) (fun j => F (finProdFinEquiv.symm i).1 j)
      (fun j => F' (finProdFinEquiv.symm i).2 j) j
  let G'' : Fin (p * p') → Fin (q + q') → X → ℝ := fun i j =>
    Fin.addCases (motive := fun _ => X → ℝ) (fun j => G (finProdFinEquiv.symm i).1 j)
      (fun j => G' (finProdFinEquiv.symm i).2 j) j
  have key : ∀ x, (∃ i, ∀ j, F'' i j x = 0 ∧ 0 < G'' i j x) ↔
      (∃ i, ∀ j, F i j x = 0 ∧ 0 < G i j x) ∧ (∃ i, ∀ j, F' i j x = 0 ∧ 0 < G' i j x) := by
    intro x
    constructor
    · rintro ⟨i, hi⟩
      refine ⟨⟨(finProdFinEquiv.symm i).1, fun j => ?_⟩, ⟨(finProdFinEquiv.symm i).2, fun j => ?_⟩⟩
      · have := hi (Fin.castAdd q' j)
        simpa only [F'', G'', Fin.addCases_left] using this
      · have := hi (Fin.natAdd q j)
        simpa only [F'', G'', Fin.addCases_right] using this
    · rintro ⟨⟨i, hi⟩, ⟨i', hi'⟩⟩
      refine ⟨finProdFinEquiv (i, i'), fun j => ?_⟩
      induction j using Fin.addCases with
      | left j =>
        simp only [F'', G'', Fin.addCases_left, Equiv.symm_apply_apply]
        exact hi j
      | right j =>
        simp only [F'', G'', Fin.addCases_right, Equiv.symm_apply_apply]
        exact hi' j
  refine ⟨V ∩ V', hVo.inter hVo', ⟨hxV, hxV'⟩, p * p', q + q', F'', G'', ?_, ?_⟩
  · intro i j
    induction j using Fin.addCases with
    | left j =>
      simp only [F'', G'', Fin.addCases_left]
      exact ⟨(hFG _ _).1.mono Set.inter_subset_left, (hFG _ _).2.mono Set.inter_subset_left⟩
    | right j =>
      simp only [F'', G'', Fin.addCases_right]
      exact ⟨(hFG' _ _).1.mono Set.inter_subset_right, (hFG' _ _).2.mono Set.inter_subset_right⟩
  · ext x
    have h := Set.ext_iff.mp hEq x
    have h' := Set.ext_iff.mp hEq' x
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_setOf_eq] at h h' ⊢
    rw [key x]
    tauto

/-- The projection of `{(x, w) ∈ Z : Ψ (x, w) ∈ S}` is subanalytic when `S` is subanalytic,
`Ψ` analytic, `Z` semianalytic, the witness `w` is a continuous function of `x`, and bounded
values of `Ψ` force bounded `(x, w)`. -/
theorem sub_proj_unique {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    {S : Set Y} (hS : IsSubanalytic S) {Ψ : X × ℝ → Y} (hΨ : ∀ z, AnalyticAt ℝ Ψ z)
    {Z : Set (X × ℝ)} (hZ : IsSemianalytic Z) {g : X → ℝ} (hg : Continuous g)
    (huniq : ∀ x w, (x, w) ∈ Z → Ψ (x, w) ∈ S → w = g x)
    (hprop : ∀ R : ℝ, ∃ R' : ℝ, ∀ x w, (x, w) ∈ Z → ‖Ψ (x, w)‖ ≤ R → ‖x‖ ≤ R' ∧ |w| ≤ R') :
    IsSubanalytic {x | ∃ w, (x, w) ∈ Z ∧ Ψ (x, w) ∈ S} := by
  intro x₀
  obtain ⟨V, hV, m, -, B, hBs, hBb, hEq⟩ := hS (Ψ (x₀, g x₀))
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun z => (hΨ z).continuousAt
  have hcont : Continuous (fun x => Ψ (x, g x)) := hΨc.comp (continuous_id.prodMk hg)
  have hU : (fun x => Ψ (x, g x)) ⁻¹' V ∈ 𝓝 x₀ := hcont.continuousAt.preimage_mem_nhds hV
  let P0 : EuclideanSpace ℝ (Fin (m + 1)) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (m + 1))
  have hP0 : ∀ v, P0 v = v 0 := fun v => rfl
  let π₁ : X × EuclideanSpace ℝ (Fin (m + 1)) → X × ℝ := fun b => (b.1, P0 b.2)
  let π₂ : X × EuclideanSpace ℝ (Fin (m + 1)) → Y × EuclideanSpace ℝ (Fin m) :=
    fun b => (Ψ (π₁ b), tailL m b.2)
  have hπ₁ : ∀ b, AnalyticAt ℝ π₁ b := fun b =>
    analyticAt_fst.prod ((P0.analyticAt _).comp analyticAt_snd)
  have hπ₂ : ∀ b, AnalyticAt ℝ π₂ b := fun b =>
    ((hΨ _).comp (hπ₁ b)).prod (((tailL m).analyticAt _).comp analyticAt_snd)
  obtain ⟨R, hR⟩ := hBb.exists_norm_le
  obtain ⟨R', hR'⟩ := hprop R
  refine ⟨(fun x => Ψ (x, g x)) ⁻¹' V, hU, m + 1, Nat.le_add_left 1 m, π₁ ⁻¹' Z ∩ π₂ ⁻¹' B,
    semi_inter (semi_preimage hπ₁ hZ) (semi_preimage hπ₂ hBs), ?_, ?_⟩
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨|R'| + |R|, fun b hb => ?_⟩
    obtain ⟨hbZ, hbB⟩ := hb
    have hn := hR _ hbB
    have hn1 : ‖Ψ (π₁ b)‖ ≤ R := (norm_fst_le _).trans hn
    have hn2 : ‖tailL m b.2‖ ≤ R := (norm_snd_le (π₂ b)).trans hn
    obtain ⟨hx, hw⟩ := hR' b.1 (P0 b.2) hbZ hn1
    rw [hP0] at hw
    have hv := norm_le_split b.2
    refine norm_prod_le_iff.2 ⟨?_, ?_⟩
    · linarith [le_abs_self R', abs_nonneg R]
    · linarith [le_abs_self R', le_abs_self R]
  · ext x
    constructor
    · rintro ⟨⟨w, hwZ, hwS⟩, hxU⟩
      have hw : w = g x := huniq x w hwZ hwS
      subst hw
      have hmem : Ψ (x, g x) ∈ S ∩ V := ⟨hwS, hxU⟩
      rw [hEq] at hmem
      obtain ⟨q, hq, hqe⟩ := hmem
      refine ⟨(x, consE (g x) q.2), ⟨?_, ?_⟩, rfl⟩
      · show (x, P0 (consE (g x) q.2)) ∈ Z
        rw [hP0, consE_zero]
        exact hwZ
      · show (Ψ (x, P0 (consE (g x) q.2)), tailL m (consE (g x) q.2)) ∈ B
        rw [hP0, consE_zero, tailL_consE, ← hqe]
        exact hq
    · rintro ⟨b, ⟨hbZ, hbB⟩, rfl⟩
      have hmem : Ψ (π₁ b) ∈ S ∩ V := by
        rw [hEq]
        exact ⟨π₂ b, hbB, rfl⟩
      have hw : P0 b.2 = g b.1 := huniq b.1 (P0 b.2) hbZ hmem.1
      refine ⟨⟨P0 b.2, hbZ, hmem.1⟩, ?_⟩
      show Ψ (b.1, g b.1) ∈ V
      rw [← hw]
      exact hmem.2

end Bdf5447aRed

open Filter Topology MoreauProx.Characterization NonsmoothLojasiewicz.Convex Bdf5447aRed in
theorem solution {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal)
    (hf : GammaZero f) (hsub : NonsmoothLojasiewicz.Continuous.IsSubanalyticFn f) (hinf : (⨅ y, f y) ≠ ⊥) :
    ∃ h : EuclideanSpace ℝ (Fin n) → ℝ,
      (∀ x, moreauEnv f x = (h x : EReal)) ∧ ContDiff ℝ 1 h ∧
        NonsmoothLojasiewicz.Continuous.IsSubanalyticFn (moreauEnv f) := by
  obtain ⟨⟨H, hH, hC1⟩, -, -, -⟩ := moreauEnv_properties f hf
  refine ⟨H, hH, hC1, ?_⟩
  have htop : (⨅ y, f y) ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hf.2.1
    exact ne_top_of_le_ne_top hx (iInf_le _ _)
  set c : ℝ := (⨅ y, f y).toReal with hc
  have hcE : ((c : ℝ) : EReal) = ⨅ y, f y := EReal.coe_toReal htop hinf
  have hcle : ∀ u, ((c : ℝ) : EReal) ≤ f u := fun u => hcE ▸ iInf_le _ u
  let P0 : EuclideanSpace ℝ (Fin (n + 1)) →L[ℝ] ℝ := EuclideanSpace.proj (0 : Fin (n + 1))
  have hP0 : ∀ v, P0 v = v 0 := fun v => rfl
  let T : Set (EuclideanSpace ℝ (Fin (n + 1))) :=
    {z | f (tailL n z) = ((c + (z 0) ^ 2 / 2 : ℝ) : EReal)}
  -- T is subanalytic: preimage of the graph of f under an analytic map
  have hT : NonsmoothLojasiewicz.Continuous.IsSubanalytic T := by
    have hZ : NonsmoothLojasiewicz.Continuous.IsSemianalytic
        {zw : EuclideanSpace ℝ (Fin (n + 1)) × ℝ | zw.2 = 0 ∧ 0 < (fun _ => (1 : ℝ)) zw} :=
      semi_basic (F := fun zw : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => zw.2)
        (G := fun _ => (1 : ℝ)) (fun _ => analyticAt_snd) (fun _ => analyticAt_const)
    let Ψ : EuclideanSpace ℝ (Fin (n + 1)) × ℝ → EuclideanSpace ℝ (Fin n) × ℝ :=
      fun zw => (tailL n zw.1, c + (P0 zw.1) ^ 2 / 2)
    have hΨ : ∀ zw, AnalyticAt ℝ Ψ zw := by
      intro zw
      have h1 : AnalyticAt ℝ (fun zw : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => tailL n zw.1) zw :=
        ((tailL n).analyticAt _).comp analyticAt_fst
      have h2 : AnalyticAt ℝ (fun zw : EuclideanSpace ℝ (Fin (n + 1)) × ℝ => P0 zw.1) zw :=
        (P0.analyticAt _).comp analyticAt_fst
      exact h1.prod (analyticAt_const.add (h2.pow 2).div_const)
    have hG := sub_proj_unique (S := {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 = (p.2 : EReal)})
      hsub hΨ hZ (g := fun _ => (0 : ℝ)) continuous_const
      (fun z w hw _ => hw.1)
      (fun R => ⟨1 + 2 * (|R| + |c|) + |R|, fun z w hw hRz => by
        have hn1 : ‖tailL n z‖ ≤ R := (norm_fst_le (Ψ (z, w))).trans hRz
        have hn2 : ‖c + (P0 z) ^ 2 / 2‖ ≤ R := (norm_snd_le (Ψ (z, w))).trans hRz
        rw [Real.norm_eq_abs, hP0] at hn2
        have h3 := le_abs_self (c + (z 0) ^ 2 / 2)
        have h4 := neg_abs_le c
        have h5 : |z 0| ≤ 1 + (z 0) ^ 2 := by
          nlinarith [abs_nonneg (z 0), sq_abs (z 0)]
        have hv := norm_le_split z
        refine ⟨by nlinarith [le_abs_self R, abs_nonneg c, sq_nonneg (z 0)], ?_⟩
        have hw0 : w = 0 := hw.1
        rw [hw0, abs_zero]
        positivity⟩)
    have hset : {x : EuclideanSpace ℝ (Fin (n + 1)) | ∃ w, (x, w) ∈
        {zw : EuclideanSpace ℝ (Fin (n + 1)) × ℝ | zw.2 = 0 ∧ 0 < (fun _ => (1 : ℝ)) zw} ∧
        Ψ (x, w) ∈ {p : EuclideanSpace ℝ (Fin n) × ℝ | f p.1 = (p.2 : EReal)}} = T := by
      ext z
      simp only [Set.mem_setOf_eq, Ψ, hP0, T]
      constructor
      · rintro ⟨w, -, hw⟩
        exact hw
      · intro hz
        exact ⟨0, ⟨rfl, one_pos⟩, hz⟩
    rw [← hset]
    exact hG
  have hd := infDist_isSubanalyticFn T hT
  -- distance identity
  have hdist : ∀ (x : EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin (n + 1))),
      dist (embL n x) a ^ 2 = (a 0) ^ 2 + ‖x - tailL n a‖ ^ 2 := by
    intro x a
    rw [dist_eq_norm, normsq_split, map_sub, embL_apply, tailL_consE]
    congr 1
    rw [PiLp.sub_apply, consE_zero]
    ring
  have hA : ∀ x, ∀ a ∈ T, 2 * (H x - c) ≤ dist (embL n x) a ^ 2 := by
    intro x a ha
    have h1 : moreauEnv f x ≤ f (tailL n a) + (((‖x - tailL n a‖ ^ 2) / 2 : ℝ) : EReal) :=
      iInf_le (fun u => f u + (((‖x - u‖ ^ 2) / 2 : ℝ) : EReal)) (tailL n a)
    have ha' : f (tailL n a) = ((c + (a 0) ^ 2 / 2 : ℝ) : EReal) := ha
    rw [hH x, ha', ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
    rw [hdist]
    linarith
  have hB : ∀ x, ∀ ε > 0, ∃ a ∈ T, dist (embL n x) a ^ 2 < 2 * (H x - c) + ε := by
    intro x ε hε
    have hlt : moreauEnv f x < ((H x + ε / 2 : ℝ) : EReal) := by
      rw [hH x, EReal.coe_lt_coe_iff]
      linarith
    obtain ⟨u, hu⟩ := iInf_lt_iff.mp hlt
    have hutop : f u ≠ ⊤ := by
      intro h
      rw [h, EReal.top_add_coe] at hu
      exact not_top_lt hu
    set r : ℝ := (f u).toReal with hr
    have hfu : f u = (r : EReal) := (EReal.coe_toReal hutop (hf.1 u)).symm
    have hrc : c ≤ r := by
      have := hcle u
      rw [hfu, EReal.coe_le_coe_iff] at this
      exact this
    rw [hfu, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hu
    refine ⟨consE (Real.sqrt (2 * (r - c))) u, ?_, ?_⟩
    · show f (tailL n (consE (Real.sqrt (2 * (r - c))) u)) =
        ((c + (consE (Real.sqrt (2 * (r - c))) u 0) ^ 2 / 2 : ℝ) : EReal)
      rw [tailL_consE, consE_zero, Real.sq_sqrt (by linarith), hfu]
      congr 1
      ring
    · rw [hdist, tailL_consE, consE_zero, Real.sq_sqrt (by linarith)]
      linarith
  have key : ∀ x, H x = c + (Metric.infDist (embL n x) T) ^ 2 / 2 := by
    intro x
    have hne : T.Nonempty := by
      obtain ⟨a, ha, -⟩ := hB x 1 one_pos
      exact ⟨a, ha⟩
    have hd0 := Metric.infDist_nonneg (x := embL n x) (s := T)
    have hle : (Metric.infDist (embL n x) T) ^ 2 ≤ 2 * (H x - c) := by
      refine le_of_forall_pos_lt_add fun ε hε => ?_
      obtain ⟨a, ha, hlt⟩ := hB x ε hε
      have h1 := Metric.infDist_le_dist_of_mem (x := embL n x) ha
      have h2 : (Metric.infDist (embL n x) T) ^ 2 ≤ dist (embL n x) a ^ 2 :=
        pow_le_pow_left₀ hd0 h1 2
      linarith
    have hge : 2 * (H x - c) ≤ (Metric.infDist (embL n x) T) ^ 2 := by
      by_contra hcon
      push Not at hcon
      have hlt : Metric.infDist (embL n x) T < Real.sqrt (2 * (H x - c)) :=
        (Real.lt_sqrt hd0).2 hcon
      obtain ⟨a, ha, hda⟩ := (Metric.infDist_lt_iff hne).1 hlt
      have h2 := (Real.lt_sqrt dist_nonneg).1 hda
      have h3 := hA x a ha
      linarith
    linarith
  -- the graph of the envelope
  have hZ : NonsmoothLojasiewicz.Continuous.IsSemianalytic
      {pw : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ |
        pw.1.2 - c - pw.2 ^ 2 / 2 = 0 ∧ 0 < (fun _ => (1 : ℝ)) pw} := by
    refine semi_basic (F := fun pw : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ => pw.1.2 - c - pw.2 ^ 2 / 2)
      (G := fun _ => (1 : ℝ)) (fun pw => ?_) (fun _ => analyticAt_const)
    have h1 : AnalyticAt ℝ (fun pw : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ => pw.1.2) pw :=
      analyticAt_snd.comp analyticAt_fst
    have h2 : AnalyticAt ℝ (fun pw : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ => pw.2) pw :=
      analyticAt_snd
    exact (h1.sub analyticAt_const).sub (h2.pow 2).div_const
  let Ψ : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ → EuclideanSpace ℝ (Fin (n + 1)) × ℝ :=
    fun pw => (embL n pw.1.1, pw.2)
  have hΨ : ∀ pw, AnalyticAt ℝ Ψ pw := by
    intro pw
    have h1 : AnalyticAt ℝ (fun pw : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ => embL n pw.1.1) pw :=
      ((embL n).analyticAt _).comp (analyticAt_fst.comp analyticAt_fst)
    exact h1.prod analyticAt_snd
  have hgc : Continuous (fun p : EuclideanSpace ℝ (Fin n) × ℝ => Metric.infDist (embL n p.1) T) :=
    (Metric.continuous_infDist_pt T).comp ((embL n).continuous.comp continuous_fst)
  have hG := sub_proj_unique
    (S := {q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ |
      ((Metric.infDist q.1 T : ℝ) : EReal) = (q.2 : EReal)})
    hd hΨ hZ hgc
    (fun p w _ hS => by
      have h : ((Metric.infDist (embL n p.1) T : ℝ) : EReal) = (w : EReal) := hS
      exact (EReal.coe_eq_coe_iff.mp h).symm)
    (fun R => ⟨|R| + |c| + R ^ 2, fun p w hw hRp => by
      have hn1 : ‖embL n p.1‖ ≤ R := (norm_fst_le (Ψ (p, w))).trans hRp
      have hn2 : ‖w‖ ≤ R := (norm_snd_le (Ψ (p, w))).trans hRp
      rw [Real.norm_eq_abs] at hn2
      have hx : ‖p.1‖ ≤ ‖embL n p.1‖ := by
        have h := normsq_split (embL n p.1)
        rw [embL_apply, consE_zero, tailL_consE] at h
        rw [embL_apply]
        nlinarith [norm_nonneg p.1, norm_nonneg (consE 0 p.1)]
      have hw2 : w ^ 2 ≤ R ^ 2 := by
        nlinarith [abs_nonneg w, sq_abs w]
      have hp2 : p.2 = c + w ^ 2 / 2 := by linarith [hw.1]
      have hab : |p.2| ≤ |c| + R ^ 2 := by
        rw [hp2]
        calc |c + w ^ 2 / 2| ≤ |c| + |w ^ 2 / 2| := abs_add_le _ _
          _ ≤ |c| + R ^ 2 := by
            rw [abs_of_nonneg (div_nonneg (sq_nonneg w) two_pos.le)]
            linarith [sq_nonneg R]
      refine ⟨norm_prod_le_iff.2 ⟨?_, ?_⟩, ?_⟩
      · nlinarith [le_abs_self R, abs_nonneg c, sq_nonneg R]
      · rw [Real.norm_eq_abs]
        linarith [abs_nonneg R]
      · nlinarith [le_abs_self R, abs_nonneg c, sq_nonneg R]⟩)
  have hset : {p : EuclideanSpace ℝ (Fin n) × ℝ | moreauEnv f p.1 = (p.2 : EReal)} =
      {p | ∃ w, (p, w) ∈ {pw : (EuclideanSpace ℝ (Fin n) × ℝ) × ℝ |
        pw.1.2 - c - pw.2 ^ 2 / 2 = 0 ∧ 0 < (fun _ => (1 : ℝ)) pw} ∧
        Ψ (p, w) ∈ {q : EuclideanSpace ℝ (Fin (n + 1)) × ℝ |
          ((Metric.infDist q.1 T : ℝ) : EReal) = (q.2 : EReal)}} := by
    ext p
    simp only [Set.mem_setOf_eq, Ψ]
    rw [hH p.1, EReal.coe_eq_coe_iff, key p.1]
    constructor
    · intro hp
      refine ⟨Metric.infDist (embL n p.1) T, ⟨by linarith, one_pos⟩, rfl⟩
    · rintro ⟨w, ⟨hw, -⟩, hwd⟩
      rw [EReal.coe_eq_coe_iff] at hwd
      rw [hwd]
      linarith
  show NonsmoothLojasiewicz.Continuous.IsSubanalytic _
  rw [hset]
  exact hG
