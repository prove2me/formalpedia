-- Prove2me | solution 1 for MartOT.Abs.fibres_le_two
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T19:02:07.134388+00:00
-- url     : https://prove2.me/submissions/6852c418-8280-4594-88dd-c49dab0d3375

import Mathlib
import Definitions.Def_MartOT_Var_Setting
import Theorems.Thm_MartOT_HN_lemma_1_11
import Theorems.Thm_MartOT_HN_lemma_3_2
import Theorems.Thm_MartOT_Opt_reroute_competitor
import Theorems.Thm_MartOT_Abs_lemma_7_5

open MeasureTheory

private lemma abs_cost_eq (ρ : Measure (ℝ × ℝ)) :
    MartOT.Var.cost (fun x y => |y - x|) ρ =
      ((∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂ρ : ENNReal) : EReal) := by
  unfold MartOT.Var.cost MartOT.Var.integralE ModelRiskOT.Duality.extIntegral
  have h1 : ∀ p : ℝ × ℝ, ((|p.2 - p.1| : ℝ) : EReal).toENNReal =
      ENNReal.ofReal |p.2 - p.1| := fun p => by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top _), EReal.toReal_coe]
  have h2 : ∀ p : ℝ × ℝ, (-((|p.2 - p.1| : ℝ) : EReal)).toENNReal = 0 := fun p => by
    apply EReal.toENNReal_of_nonpos
    rw [← EReal.coe_neg]
    exact_mod_cast neg_nonpos.mpr (abs_nonneg _)
  simp only [h1, h2, lintegral_zero, EReal.coe_ennreal_zero, sub_zero]

private lemma abs_lint3 (a b c : ℝ × ℝ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) :
    (∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂(ENNReal.ofReal r • Measure.dirac a +
      ENNReal.ofReal s • Measure.dirac b + Measure.dirac c)) =
      ENNReal.ofReal (r * |a.2 - a.1| + s * |b.2 - b.1| + |c.2 - c.1|) := by
  rw [lintegral_add_measure, lintegral_add_measure, lintegral_smul_measure,
    lintegral_smul_measure, lintegral_dirac, lintegral_dirac, lintegral_dirac, smul_eq_mul,
    smul_eq_mul, ← ENNReal.ofReal_mul hr, ← ENNReal.ofReal_mul hs,
    ← ENNReal.ofReal_add (mul_nonneg hr (abs_nonneg _)) (mul_nonneg hs (abs_nonneg _)),
    ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hr (abs_nonneg _))
      (mul_nonneg hs (abs_nonneg _))) (abs_nonneg _)]

/-- On a finitely optimal set `Γ` for `c(x, y) = |y - x|`, any rerouting of three points
`(X, ym), (X, yp), (X', y') ∈ Γ` with `ym < y' < yp` and `X ≠ X'` satisfies `A(X') ≤ B(X')`. -/
private lemma abs_reroute_le (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => |y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => |y - x|) α')
    (X ym yp X' y' : ℝ) (hm : (X, ym) ∈ Γ) (hp : (X, yp) ∈ Γ) (h' : (X', y') ∈ Γ)
    (hy : ym < y' ∧ y' < yp) (hX : X ≠ X') :
    let l := (y' - ym) / (yp - ym)
    l * |X - yp| + (1 - l) * |X - ym| + |X' - y'| ≤
      l * |X' - yp| + (1 - l) * |X' - ym| + |X - y'| := by
  set l := (y' - ym) / (yp - ym) with hl
  have hd : 0 < yp - ym := by linarith
  have hl0 : 0 < l := div_pos (by linarith) hd
  have hl1 : l < 1 := by rw [hl, div_lt_one hd]; linarith
  have hcomb : l * yp + (1 - l) * ym = y' := by
    rw [hl]; field_simp; ring
  have hcomp := MartOT.Opt.reroute_competitor X X' ym yp y' l hl0 hl1 hcomb
  have hne1 : (X, yp) ≠ (X, ym) := fun h => by
    have := (Prod.mk.inj h).2; linarith
  have hne2 : (X, yp) ≠ (X', y') := fun h => hX (Prod.mk.inj h).1
  have hne3 : (X, ym) ≠ (X', y') := fun h => hX (Prod.mk.inj h).1
  set w : ℝ × ℝ → NNReal := fun p =>
    if p = (X, yp) then Real.toNNReal l else if p = (X, ym) then Real.toNNReal (1 - l) else 1
    with hw
  have hsum : (∑ p ∈ ({(X, yp), (X, ym), (X', y')} : Finset (ℝ × ℝ)),
      (w p : ENNReal) • Measure.dirac p) =
      ENNReal.ofReal l • Measure.dirac (X, yp) + ENNReal.ofReal (1 - l) • Measure.dirac (X, ym) +
        Measure.dirac (X', y') := by
    rw [Finset.sum_insert (by simp [hne1, hne2]), Finset.sum_insert (by simp [hne3]),
      Finset.sum_singleton]
    simp only [hw, if_pos rfl, if_neg hne1.symm, if_neg hne2.symm, if_neg hne3.symm, ENNReal.coe_one,
      one_smul]
    rw [add_assoc]
    rfl
  have hsub : (↑({(X, yp), (X, ym), (X', y')} : Finset (ℝ × ℝ)) : Set (ℝ × ℝ)) ⊆ Γ := by
    intro q hq
    simp only [Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
      Set.mem_singleton_iff] at hq
    rcases hq with rfl | rfl | rfl <;> assumption
  have key := hΓ _ w hsub _ (by rw [hsum]; exact hcomp)
  rw [hsum, abs_cost_eq, abs_cost_eq, EReal.coe_ennreal_le_coe_ennreal_iff,
    abs_lint3 _ _ _ _ _ hl0.le (by linarith),
    abs_lint3 _ _ _ _ _ (by linarith) hl0.le,
    ENNReal.ofReal_le_ofReal_iff (by positivity)] at key
  simp only at key
  have h1 : |yp - X| = |X - yp| := abs_sub_comm _ _
  have h2 : |ym - X| = |X - ym| := abs_sub_comm _ _
  have h3 : |y' - X'| = |X' - y'| := abs_sub_comm _ _
  have h4 : |ym - X'| = |X' - ym| := abs_sub_comm _ _
  have h5 : |yp - X'| = |X' - yp| := abs_sub_comm _ _
  have h6 : |y' - X| = |X - y'| := abs_sub_comm _ _
  rw [h1, h2, h3, h4, h5, h6] at key
  linarith

/-- Forbidden configurations from (24): on a finitely optimal `Γ` for `c(x, y) = |y - x|`,
given `(X, ym), (X, yp), (X', y') ∈ Γ` with `ym < X < yp` and `ym < y' < yp`,
we cannot have `y' < X < X'` or `X' < X < y'`. -/
private lemma abs_forb (Γ : Set (ℝ × ℝ))
    (hΓ : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => |y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => |y - x|) α')
    (X ym yp X' y' : ℝ) (hm : (X, ym) ∈ Γ) (hp : (X, yp) ∈ Γ) (h' : (X', y') ∈ Γ)
    (hx : ym < X ∧ X < yp) (hy : ym < y' ∧ y' < yp) :
    ¬ (y' < X ∧ X < X') ∧ ¬ (X' < X ∧ X < y') := by
  set l := (y' - ym) / (yp - ym) with hl
  have hd : 0 < yp - ym := by linarith
  have hcomb : l * yp + (1 - l) * ym = y' := by
    rw [hl]; field_simp; ring
  set A : ℝ → ℝ := fun z => l * |X - yp| + (1 - l) * |X - ym| + |z - y'|
  set B : ℝ → ℝ := fun z => l * |z - yp| + (1 - l) * |z - ym| + |X - y'|
  have h75 := MartOT.Abs.lemma_7_5 X ym yp y' l hx hy hcomb A B (fun _ => rfl) (fun _ => rfl)
  constructor
  · rintro ⟨hyX, hXX'⟩
    have hle : A X' ≤ B X' := abs_reroute_le Γ hΓ X ym yp X' y' hm hp h' hy (ne_of_lt hXX')
    obtain ⟨x0, -, -, hpos, -⟩ := h75.1 hyX
    have hnot : X' ∉ Set.Icc x0 X := fun h => not_le_of_gt hXX' h.2
    linarith [hpos X' hnot]
  · rintro ⟨hX'X, hXy'⟩
    have hle : A X' ≤ B X' := abs_reroute_le Γ hΓ X ym yp X' y' hm hp h' hy (ne_of_gt hX'X)
    obtain ⟨x1, -, -, hpos, -⟩ := h75.2.1 hXy'
    have hnot : X' ∉ Set.Icc X x1 := fun h => not_le_of_gt hX'X h.1
    linarith [hpos X' hnot]

/-- Martingale property: if on `K` (of full `π`-measure) we have `s * (y - x) ≥ 0` whenever
`x ∈ D`, then no `π`-mass in `K ∩ (D × ℝ)` can lie off the diagonal. -/
private lemma abs_one_sided_null {μ ν : Measure ℝ} {π : Measure (ℝ × ℝ)}
    (hπ : MartOT.Var.IsMartingalePlan μ ν π) (K : Set (ℝ × ℝ)) (hK : π Kᶜ = 0)
    (D : Set ℝ) (hD : MeasurableSet D) (s : ℝ) (hs : s = 1 ∨ s = -1)
    (hge : ∀ p ∈ K, p.1 ∈ D → 0 ≤ s * (p.2 - p.1)) :
    π (K ∩ Prod.fst ⁻¹' D ∩ {p : ℝ × ℝ | p.2 ≠ p.1}) = 0 := by
  have hint := hπ.2.1
  have hm := hπ.2.2
  set ρ : ℝ → ℝ := fun x => s * D.indicator (fun _ => (1 : ℝ)) x with hρ
  set f : ℝ × ℝ → ℝ := fun p => ρ p.1 * (p.2 - p.1) with hf
  have hρm : Measurable ρ := (measurable_const.indicator hD).const_mul s
  have hs_abs : |s| = 1 := by rcases hs with rfl | rfl <;> simp
  have hs_ne : s ≠ 0 := by rcases hs with rfl | rfl <;> norm_num
  have hρb : ∃ C, ∀ x, |ρ x| ≤ C := by
    refine ⟨1, fun x => ?_⟩
    rw [hρ, abs_mul, hs_abs, one_mul]
    by_cases hx : x ∈ D <;> simp [hx]
  have hzero : ∫ p, f p ∂π = 0 := hm ρ hρm hρb
  have hfint : Integrable f π := by
    obtain ⟨C, hC⟩ := hρb
    refine hint.bdd_mul (c := C) (hρm.comp measurable_fst).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun p => by simpa [Real.norm_eq_abs] using hC p.1
  have hKae : ∀ᵐ p ∂π, p ∈ K := by
    rw [ae_iff]; simpa [Set.compl_def] using hK
  have hnn : 0 ≤ᵐ[π] f := by
    filter_upwards [hKae] with p hp
    by_cases hpD : p.1 ∈ D
    · simp only [hf, hρ, Pi.zero_apply, Set.indicator_of_mem hpD, mul_one]
      exact hge p hp hpD
    · simp [hf, hρ, Set.indicator_of_notMem hpD]
  have hf0 := (integral_eq_zero_iff_of_nonneg_ae hnn hfint).mp hzero
  have hae : ∀ᵐ p ∂π, p ∉ K ∩ Prod.fst ⁻¹' D ∩ {p : ℝ × ℝ | p.2 ≠ p.1} := by
    filter_upwards [hf0] with p hfp ⟨⟨_, hpD⟩, hne⟩
    simp only [hf, hρ, Pi.zero_apply, Set.indicator_of_mem (show p.1 ∈ D from hpD), mul_one] at hfp
    have hdiff : p.2 - p.1 = 0 := (mul_eq_zero.mp hfp).resolve_left hs_ne
    exact hne (sub_eq_zero.mp hdiff)
  exact measure_eq_zero_iff_ae_notMem.mpr hae

/-- Projections of `σ`-compact sets intersected with `F_σ` sets are Borel. -/
private lemma abs_proj_fSigma_meas (Kn : ℕ → Set (ℝ × ℝ)) (hKn : ∀ n, IsCompact (Kn n))
    (Lm : ℕ → Set (ℝ × ℝ)) (hLm : ∀ m, IsClosed (Lm m)) :
    MeasurableSet (Prod.fst '' ((⋃ n, Kn n) ∩ (⋃ m, Lm m))) := by
  have heq : (⋃ n, Kn n) ∩ (⋃ m, Lm m) = ⋃ n, ⋃ m, (Kn n ∩ Lm m) := by
    ext p; simp [Set.mem_iUnion]
  rw [heq, Set.image_iUnion]
  refine MeasurableSet.iUnion fun n => ?_
  rw [Set.image_iUnion]
  exact MeasurableSet.iUnion fun m =>
    (((hKn n).inter_right (hLm m)).image continuous_fst).isClosed.measurableSet

theorem solution (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμν : MartOT.Var.ConvexLE μ ν) (hμc : ∀ x : ℝ, μ {x} = 0) (π : Measure (ℝ × ℝ))
    (hπ : MartOT.Var.IsOptimal (fun x y => |y - x|) μ ν π) :
    ∃ Γ : Set (ℝ × ℝ), MeasurableSet Γ ∧ π Γᶜ = 0 ∧
      ∀ x : ℝ, {y : ℝ | (x, y) ∈ Γ ∧ y ≠ x}.encard ≤ 2 := by
  have hmp := hπ.1
  -- Step 1: Apply Lemma 1.11 to `c(x, y) = |y - x|`
  have hcm : Measurable (Function.uncurry fun x y : ℝ => |y - x|) := by
    show Measurable (fun p : ℝ × ℝ => |p.2 - p.1|)
    fun_prop
  have hint : MartOT.Var.SuffIntegrable μ ν (fun x y => |y - x|) :=
    ⟨fun _ => 0, fun _ => 0, integrable_zero _ _ _, integrable_zero _ _ _,
      fun x y => by simp [abs_nonneg]⟩
  have hfin : MartOT.Var.cost (fun x y => |y - x|) π < ⊤ := by
    rw [abs_cost_eq]
    have hlt : (∫⁻ p, ENNReal.ofReal |p.2 - p.1| ∂π) < ⊤ := by
      have h2 := hmp.2.1.2
      simp only [HasFiniteIntegral, Real.enorm_eq_ofReal_abs] at h2
      exact h2
    exact lt_top_iff_ne_top.mpr (by simp [hlt.ne])
  obtain ⟨Γ0, hΓ0m, hΓ0c, hΓ0v⟩ := MartOT.HN.lemma_1_11 μ ν hμν _ hcm hint π hπ hfin
  -- Step 2: Inner regularity gives a `σ`-compact `K ⊆ Γ0` of full `π`-measure
  have huniv : π Set.univ = 1 := by
    rw [← Set.preimage_univ (f := Prod.fst), ← Measure.map_apply measurable_fst MeasurableSet.univ,
      hmp.1.1]
    simp
  have hfinΓ : π Γ0 ≠ ⊤ :=
    ne_top_of_le_ne_top (by rw [huniv]; simp) (measure_mono (Set.subset_univ _))
  have hcpt : ∀ n : ℕ, ∃ Kn, Kn ⊆ Γ0 ∧ IsCompact Kn ∧ π (Γ0 \ Kn) < (1 / ((n : ENNReal) + 1)) :=
    fun n => hΓ0m.exists_isCompact_sdiff_lt hfinΓ (by simp)
  choose Kn hKnsub hKncpt hKnlt using hcpt
  set K := ⋃ n, Kn n with hKdef
  have hKm : MeasurableSet K := MeasurableSet.iUnion fun n => (hKncpt n).measurableSet
  have hKsub : K ⊆ Γ0 := Set.iUnion_subset hKnsub
  have hKc : π Kᶜ = 0 := by
    have h1 : π (Γ0 \ K) = 0 := by
      refine le_antisymm (le_of_forall_pos_le_add fun ε hε => ?_) bot_le
      obtain ⟨n, hn⟩ := ENNReal.exists_inv_nat_lt hε.ne'
      calc π (Γ0 \ K) ≤ π (Γ0 \ Kn n) :=
            measure_mono (Set.sdiff_subset_sdiff_right (Set.subset_iUnion Kn n))
        _ ≤ 1 / ((n : ENNReal) + 1) := (hKnlt n).le
        _ ≤ (n : ENNReal)⁻¹ := by
            rw [one_div]; exact ENNReal.inv_le_inv.mpr le_self_add
        _ ≤ 0 + ε := by rw [zero_add]; exact hn.le
    have : Kᶜ ⊆ Γ0ᶜ ∪ (Γ0 \ K) := by
      intro p hp
      by_cases h : p ∈ Γ0
      · exact Or.inr ⟨h, hp⟩
      · exact Or.inl h
    exact measure_mono_null this (measure_union_null hΓ0c h1)
  -- Step 3: Strict-side projections are Borel via `F_σ` decomposition
  set Llt_m : ℕ → Set (ℝ × ℝ) := fun m => {p | p.2 + 1 / ((m : ℝ) + 1) ≤ p.1}
  set Lgt_m : ℕ → Set (ℝ × ℝ) := fun m => {p | p.1 + 1 / ((m : ℝ) + 1) ≤ p.2}
  have hLlt_c : ∀ m, IsClosed (Llt_m m) := fun m =>
    isClosed_le (continuous_snd.add continuous_const) continuous_fst
  have hLgt_c : ∀ m, IsClosed (Lgt_m m) := fun m =>
    isClosed_le (continuous_fst.add continuous_const) continuous_snd
  have hLlt_eq : (⋃ m, Llt_m m) = {p : ℝ × ℝ | p.2 < p.1} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Llt_m]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    · intro hlt
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      exact ⟨m, by linarith⟩
  have hLgt_eq : (⋃ m, Lgt_m m) = {p : ℝ × ℝ | p.1 < p.2} := by
    ext p
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, Lgt_m]
    constructor
    · rintro ⟨m, hm⟩
      have hpos : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
      linarith
    · intro hlt
      obtain ⟨m, hm⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      exact ⟨m, by linarith⟩
  set Plt := Prod.fst '' (K ∩ {p : ℝ × ℝ | p.2 < p.1}) with hPlt
  set Pgt := Prod.fst '' (K ∩ {p : ℝ × ℝ | p.1 < p.2}) with hPgt
  have hPltm : MeasurableSet Plt := by
    rw [hPlt, hKdef, ← hLlt_eq]
    exact abs_proj_fSigma_meas Kn hKncpt Llt_m hLlt_c
  have hPgtm : MeasurableSet Pgt := by
    rw [hPgt, hKdef, ← hLgt_eq]
    exact abs_proj_fSigma_meas Kn hKncpt Lgt_m hLgt_c
  -- Step 4: Remove one-sided off-diagonal points using the martingale property
  have hnull_lt : π (K ∩ Prod.fst ⁻¹' Pltᶜ ∩ {p : ℝ × ℝ | p.2 ≠ p.1}) = 0 := by
    refine abs_one_sided_null hmp K hKc Pltᶜ hPltm.compl 1 (Or.inl rfl) fun p hpK hpD => ?_
    have hnot : ¬ p.2 < p.1 := fun h => hpD ⟨p, ⟨hpK, h⟩, rfl⟩
    linarith [not_lt.mp hnot]
  have hnull_gt : π (K ∩ Prod.fst ⁻¹' Pgtᶜ ∩ {p : ℝ × ℝ | p.2 ≠ p.1}) = 0 := by
    refine abs_one_sided_null hmp K hKc Pgtᶜ hPgtm.compl (-1) (Or.inr rfl) fun p hpK hpD => ?_
    have hnot : ¬ p.1 < p.2 := fun h => hpD ⟨p, ⟨hpK, h⟩, rfl⟩
    linarith [not_lt.mp hnot]
  set Δ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 = p.1}
  have hΔm : MeasurableSet Δ := isClosed_eq continuous_snd continuous_fst |>.measurableSet
  set Γ1 : Set (ℝ × ℝ) := (K ∩ Δ) ∪ (K ∩ Prod.fst ⁻¹' (Plt ∩ Pgt)) with hΓ1
  have hΓ1m : MeasurableSet Γ1 :=
    (hKm.inter hΔm).union (hKm.inter (measurable_fst (hPltm.inter hPgtm)))
  have hΓ1sub : Γ1 ⊆ Γ0 := Set.union_subset (Set.inter_subset_left.trans hKsub)
    (Set.inter_subset_left.trans hKsub)
  have hΓ1v : ∀ (S : Finset (ℝ × ℝ)) (w : ℝ × ℝ → NNReal), (↑S : Set (ℝ × ℝ)) ⊆ Γ1 →
      ∀ α' : Measure (ℝ × ℝ),
        MartOT.Var.IsCompetitor (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) α' →
        MartOT.Var.cost (fun x y => |y - x|) (∑ p ∈ S, (w p : ENNReal) • Measure.dirac p) ≤
          MartOT.Var.cost (fun x y => |y - x|) α' :=
    fun S w hS α' hc => hΓ0v S w (hS.trans hΓ1sub) α' hc
  have hΓ1c : π Γ1ᶜ = 0 := by
    have hsub : Γ1ᶜ ⊆ Kᶜ ∪ (K ∩ Prod.fst ⁻¹' Pltᶜ ∩ {p : ℝ × ℝ | p.2 ≠ p.1}) ∪
        (K ∩ Prod.fst ⁻¹' Pgtᶜ ∩ {p : ℝ × ℝ | p.2 ≠ p.1}) := by
      intro p hp
      by_cases hpK : p ∈ K
      · have hne : p.2 ≠ p.1 := fun heq => hp (Or.inl ⟨hpK, heq⟩)
        have hnotP : p.1 ∉ Plt ∩ Pgt := fun h => hp (Or.inr ⟨hpK, h⟩)
        rcases not_and_or.mp hnotP with h1 | h2
        · exact Or.inl (Or.inr ⟨⟨hpK, h1⟩, hne⟩)
        · exact Or.inr ⟨⟨hpK, h2⟩, hne⟩
      · exact Or.inl (Or.inl hpK)
    exact measure_mono_null hsub (measure_union_null (measure_union_null hKc hnull_lt) hnull_gt)
  -- Strict straddling for every off-diagonal point of `Γ1`
  have hΓ1str : ∀ a y : ℝ, (a, y) ∈ Γ1 → y ≠ a →
      (∃ y1 : ℝ, (a, y1) ∈ Γ1 ∧ y1 < a) ∧ (∃ y2 : ℝ, (a, y2) ∈ Γ1 ∧ a < y2) := by
    intro a y hay hne
    have haP : a ∈ Plt ∩ Pgt := by
      rcases hay with ⟨-, heq⟩ | ⟨-, haP⟩
      · exact absurd heq hne
      · exact haP
    obtain ⟨⟨q, ⟨hqK, hqlt⟩, hqa⟩, ⟨r, ⟨hrK, hrgt⟩, hra⟩⟩ := id haP
    have hqeq : (a, q.2) = q := Prod.ext hqa.symm rfl
    have hreq : (a, r.2) = r := Prod.ext hra.symm rfl
    refine ⟨⟨q.2, Or.inr ⟨hqeq.symm ▸ hqK, haP⟩, ?_⟩,
      ⟨r.2, Or.inr ⟨hreq.symm ▸ hrK, haP⟩, ?_⟩⟩
    · have : q.2 < q.1 := hqlt
      linarith
    · have : r.1 < r.2 := hrgt
      linarith
  -- Step 5: Show `A = {a | 2 < |(Γ1 \ Δ)_a|}` is countable using Lemma 3.2 and (24)
  set Γbar : Set (ℝ × ℝ) := {p : ℝ × ℝ | p ∈ Γ1 ∧ p.2 ≠ p.1} with hΓbar
  set A : Set ℝ := {a : ℝ | 2 < {y : ℝ | (a, y) ∈ Γbar}.encard} with hA
  have hAc : A.Countable := by
    by_contra hunc
    have hA3 : {a : ℝ | ((3 : ℕ) : ℕ∞) ≤ {y : ℝ | (a, y) ∈ Γbar}.encard} = A := by
      ext a
      simp only [Set.mem_ofPred_eq, hA]
      constructor
      · intro h; exact lt_of_lt_of_le (by norm_num) h
      · intro h
        exact (ENat.add_one_le_iff (by decide : (2 : ℕ∞) ≠ ⊤)).mpr h
    obtain ⟨a, b, hb, hbΓ, happ⟩ :=
      MartOT.HN.lemma_3_2 3 (by norm_num) Γbar (by rw [hA3]; exact hunc)
    have h01 : b 0 < b 1 := hb (by decide)
    have h12 : b 1 < b 2 := hb (by decide)
    have hb0 : (a, b 0) ∈ Γ1 := (hbΓ 0).1
    have hb1 : (a, b 1) ∈ Γ1 := (hbΓ 1).1
    have hb2 : (a, b 2) ∈ Γ1 := (hbΓ 2).1
    have hb1_ne : b 1 ≠ a := (hbΓ 1).2
    rcases lt_or_gt_of_ne hb1_ne with hlt | hgt
    · -- Case 1: `b 1 < a`. Use `y2 > a` from strict straddling and a right approximation.
      obtain ⟨-, y2, hy2, hay2⟩ := hΓ1str a (b 1) hb1 hb1_ne
      set ε := min (b 1 - b 0) (a - b 1) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
      have hε1 : ε ≤ (b 1 - b 0) / 2 := by rw [hε]; linarith [min_le_left (b 1 - b 0) (a - b 1)]
      have hε2 : ε ≤ (a - b 1) / 2 := by rw [hε]; linarith [min_le_right (b 1 - b 0) (a - b 1)]
      obtain ⟨a', ha', b', -, hb'Γ, -, hdb⟩ := (happ ε hε0).1
      have eb1 := abs_lt.mp (hdb 1)
      have hforb := abs_forb Γ1 hΓ1v a (b 0) y2 a' (b' 1) hb0 hy2 (hb'Γ 1).1
        ⟨by linarith, hay2⟩ ⟨by linarith, by linarith⟩
      exact hforb.1 ⟨by linarith, ha'⟩
    · -- Case 2: `a < b 1`. Use `y1 < a` from strict straddling and a left approximation.
      obtain ⟨⟨y1, hy1, hy1a⟩, -⟩ := hΓ1str a (b 1) hb1 hb1_ne
      set ε := min (b 2 - b 1) (b 1 - a) / 2 with hε
      have hε0 : 0 < ε := by rw [hε]; exact half_pos (lt_min (by linarith) (by linarith))
      have hε1 : ε ≤ (b 2 - b 1) / 2 := by rw [hε]; linarith [min_le_left (b 2 - b 1) (b 1 - a)]
      have hε2 : ε ≤ (b 1 - a) / 2 := by rw [hε]; linarith [min_le_right (b 2 - b 1) (b 1 - a)]
      obtain ⟨a'', ha'', b'', -, hb''Γ, -, hdb⟩ := (happ ε hε0).2
      have eb1 := abs_lt.mp (hdb 1)
      have hforb := abs_forb Γ1 hΓ1v a y1 (b 2) a'' (b'' 1) hy1 hb2 (hb''Γ 1).1
        ⟨hy1a, by linarith⟩ ⟨by linarith, by linarith⟩
      exact hforb.2 ⟨ha'', by linarith⟩
  -- Step 6: Remove `A × ℝ` (null since `A` is countable and `μ` is atomless)
  have hAm : MeasurableSet A := hAc.measurableSet
  have hA0 : μ A = 0 := by
    rw [← Set.biUnion_of_singleton A]
    exact (measure_biUnion_null_iff hAc).2 fun a _ => hμc a
  refine ⟨Γ1 ∩ Prod.fst ⁻¹' Aᶜ, hΓ1m.inter (measurable_fst hAm.compl), ?_, ?_⟩
  · rw [Set.compl_inter, ← Set.preimage_compl, compl_compl]
    refine measure_union_null hΓ1c ?_
    rw [← Measure.map_apply measurable_fst hAm, hmp.1.1]
    exact hA0
  · intro x
    by_cases hx : x ∈ A
    · have hempty : {y : ℝ | (x, y) ∈ Γ1 ∩ Prod.fst ⁻¹' Aᶜ ∧ y ≠ x} = ∅ := by
        ext y; simp [hx]
      rw [hempty]; simp
    · have hsub : {y : ℝ | (x, y) ∈ Γ1 ∩ Prod.fst ⁻¹' Aᶜ ∧ y ≠ x} ⊆
          {y : ℝ | (x, y) ∈ Γbar} := fun y hy => ⟨hy.1.1, hy.2⟩
      exact le_trans (Set.encard_le_encard hsub) (not_lt.mp hx)
