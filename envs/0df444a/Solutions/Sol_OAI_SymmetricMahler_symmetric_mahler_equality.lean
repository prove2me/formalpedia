-- Prove2me | solution 1 for OAI.SymmetricMahler.symmetric_mahler_equality
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T01:37:08.644737+00:00
-- url     : https://prove2.me/submissions/b12b65b5-3b8e-4ce5-9fc2-35f91721ee45

import Mathlib
import Definitions.Def_SymmetricMahlerEquality
import Definitions.Def_OAIQ2Ma000
import Theorems.Thm_OAI_SymmetricMahler_equality_polar_gauge_medians_eq

section
-- module Solutions.OAIQ2_Mah.Mahler_HannerBodies
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set MeasureTheory

namespace RealNormData
open MeasureTheory.Measure
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma unit_max (g : RealNormData E) (h : RealNormData F) :
    (g.max h).unit = g.unit ×ˢ h.unit := by ext x; simp [unit]

lemma convex_unit (g : RealNormData E) : Convex ℝ g.unit := by
  intro x hx y hy a b ha hb hab
  change g (a • x + b • y) ≤ 1
  calc
    g (a • x + b • y) ≤ g (a • x) + g (b • y) := g.add_le _ _
    _ = a * g x + b * g y := by rw [g.smul_eq, g.smul_eq, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hx ha)
      (mul_le_mul_of_nonneg_left hy hb)
    _ = 1 := by linarith

lemma exists_smul_unit (g : RealNormData E) {r : ℝ} (hr : 0 ≤ r) {x : E} (hx : g x ≤ r) :
    ∃ u ∈ g.unit, x = r • u := by
  obtain rfl | hr := hr.eq_or_lt
  · have hx0 : x = 0 := g.eq_zero.mp (le_antisymm hx (g.nonneg x))
    exact ⟨0, g.zero_mem_unit, by simp [hx0]⟩
  refine ⟨r⁻¹ • x, ?_, ?_⟩
  · change g (r⁻¹ • x) ≤ 1
    rw [g.smul_eq, abs_of_pos (inv_pos.mpr hr)]
    exact (inv_mul_le_one₀ hr).mpr hx
  · simp [smul_smul, ne_of_gt hr]

lemma unit_sum (g : RealNormData E) (h : RealNormData F) :
    (g.sum h).unit = convexHull ℝ
      (((fun x : E => (x, (0:F))) '' g.unit) ∪ ((fun y : F => ((0:E), y)) '' h.unit)) := by
  apply subset_antisymm
  · rintro ⟨x,y⟩ hxy
    change g x + h y ≤ 1 at hxy
    obtain ⟨u, hu, hx⟩ := g.exists_smul_unit (g.nonneg x) (le_refl (g x))
    obtain ⟨v, hv, hy⟩ := h.exists_smul_unit (show 0 ≤ 1-g x by linarith [h.nonneg y])
      (show h y ≤ 1-g x by linarith)
    have hh := (convex_convexHull ℝ
      (((fun x : E => (x, (0:F))) '' g.unit) ∪ ((fun y : F => ((0:E), y)) '' h.unit)))
      (subset_convexHull ℝ _ (Or.inl ⟨u,hu,rfl⟩))
      (subset_convexHull ℝ _ (Or.inr ⟨v,hv,rfl⟩))
      (g.nonneg x) (show 0 ≤ 1-g x by linarith [h.nonneg y]) (by ring : g x + (1-g x) = 1)
    convert hh using 1
    ext <;> simp [←hx, ←hy]
  · apply convexHull_min _ (g.sum h).convex_unit
    rintro _ (⟨x,hx,rfl⟩ | ⟨y,hy,rfl⟩)
    · simpa only [unit, Set.mem_ofPred_eq, sum_apply, apply_zero, add_zero] using hx
    · simpa only [unit, Set.mem_ofPred_eq, sum_apply, apply_zero, zero_add] using hy

lemma unit_comap (g : RealNormData E) (e : F ≃ₗ[ℝ] E) :
    (g.comap e).unit = e.symm '' g.unit := by
  ext x
  constructor
  · intro hx
    exact ⟨e x, hx, e.symm_apply_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [unit, comap_apply, Set.mem_ofPred_eq, e.apply_symm_apply] using hy

variable [inst423 : TopologicalSpace E] [inst424 : IsTopologicalAddGroup E] [inst425 : T2Space E] [inst426 : ContinuousSMul ℝ E]
  [MeasurableSpace E] [inst428 : BorelSpace E] [inst429 : FiniteDimensional ℝ E] [inst430 : SecondCountableTopology E]
  [inst431 : TopologicalSpace F] [inst432 : IsTopologicalAddGroup F] [inst433 : T2Space F] [inst434 : ContinuousSMul ℝ F]
  [MeasurableSpace F] [inst436 : BorelSpace F] [inst437 : FiniteDimensional ℝ F] [inst438 : SecondCountableTopology F]

omit inst430 in
lemma measure_unit [SecondCountableTopology E] (g : RealNormData E) (μ : Measure E) [IsAddHaarMeasure μ] [Nontrivial E] :
    μ g.unit = ENNReal.ofReal ((∫ x, Real.exp (-g x) ∂μ) / (Nat.factorial (Module.finrank ℝ E) : ℝ)) := by
  rw [unit, MeasureTheory.measure_le_eq_lt μ g.apply_zero g.apply_neg g.add_le
    (fun hx => g.eq_zero.mp hx) (fun a x => (g.smul_eq a x).le) 1]
  have hh := MeasureTheory.measure_lt_one_eq_integral_div_gamma μ g.apply_zero g.apply_neg g.add_le
    (fun hx => g.eq_zero.mp hx) (fun a x => (g.smul_eq a x).le) (show (0:ℝ) < 1 by norm_num)
  simpa only [div_one, Real.rpow_one, Real.Gamma_nat_eq_factorial] using hh

lemma measureReal_unit (g : RealNormData E) (μ : Measure E) [IsAddHaarMeasure μ] [Nontrivial E] :
    (μ g.unit).toReal = (∫ x, Real.exp (-g x) ∂μ) / (Nat.factorial (Module.finrank ℝ E) : ℝ) := by
  rw [g.measure_unit μ, ENNReal.toReal_ofReal]
  exact div_nonneg (integral_nonneg fun _ => (Real.exp_pos _).le) (by positivity)

lemma measureReal_unit_sum (g : RealNormData E) (h : RealNormData F)
    (μ : Measure E) (ν : Measure F) [IsAddHaarMeasure μ] [IsAddHaarMeasure ν]
    [SigmaFinite μ] [SigmaFinite ν] [Nontrivial E] [Nontrivial F] :
    ((μ.prod ν) (g.sum h).unit).toReal =
      (Nat.factorial (Module.finrank ℝ E) : ℝ) * Nat.factorial (Module.finrank ℝ F) /
        Nat.factorial (Module.finrank ℝ E + Module.finrank ℝ F) *
      (μ g.unit).toReal * (ν h.unit).toReal := by
  rw [(g.sum h).measureReal_unit, g.measureReal_unit, h.measureReal_unit]
  simp_rw [sum_apply, neg_add, Real.exp_add]
  rw [integral_prod_mul (μ := μ) (ν := ν) (fun x : E => Real.exp (-g x))
    (fun y : F => Real.exp (-h y)), Module.finrank_prod]
  have hE : (Nat.factorial (Module.finrank ℝ E) : ℝ) ≠ 0 := by positivity
  have hF : (Nat.factorial (Module.finrank ℝ F) : ℝ) ≠ 0 := by positivity
  field_simp

omit inst423 inst424 inst425 inst426 inst428 inst429 inst430 inst431 inst432 inst433 inst434 inst436 inst437 inst438 in
lemma measureReal_unit_max [TopologicalSpace E] [IsTopologicalAddGroup E] [T2Space E] [ContinuousSMul ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [SecondCountableTopology E] [TopologicalSpace F] [IsTopologicalAddGroup F] [T2Space F] [ContinuousSMul ℝ F] [BorelSpace F] [FiniteDimensional ℝ F] [SecondCountableTopology F] (g : RealNormData E) (h : RealNormData F)
    (μ : Measure E) (ν : Measure F) [SigmaFinite ν] :
    ((μ.prod ν) (g.max h).unit).toReal = (μ g.unit).toReal * (ν h.unit).toReal := by
  rw [unit_max, Measure.prod_prod, ENNReal.toReal_mul]

end RealNormData

lemma measurePreserving_appendEquiv (k l : ℕ) : MeasurePreserving (appendEquiv k l) := by
  let e₁ := (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ Fin l => ℝ)).symm
  let e₂ := MeasurableEquiv.piCongrLeft (fun _ : Fin (k+l) => ℝ) (finSumFinEquiv : Fin k ⊕ Fin l ≃ _)
  have h₁ : MeasurePreserving e₁ := volume_measurePreserving_sumPiEquivProdPi_symm _
  have h₂ : MeasurePreserving e₂ := volume_measurePreserving_piCongrLeft _ _
  convert h₂.comp h₁ using 1
  funext z i
  refine Fin.addCases (fun _ => ?_) (fun _ => ?_) i <;>
    simp [e₁, e₂, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft, Equiv.piCongrLeft',
      MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi, appendEquiv]

lemma volume_appendEquiv_image {k l : ℕ} (S : Set ((Fin k → ℝ) × (Fin l → ℝ))) :
    volume (appendEquiv k l '' S) = volume S :=
  by
    have hh := (measurePreserving_appendEquiv k l).measure_preimage_emb
      (appendEquiv k l).toContinuousLinearEquiv.toHomeomorph.measurableEmbedding
      (appendEquiv k l '' S)
    rw [Set.preimage_image_eq _ (appendEquiv k l).injective] at hh
    exact hh.symm

lemma dot_append {k l : ℕ} (x p : Fin k → ℝ) (y q : Fin l → ℝ) :
    (∑ i, Fin.append p q i * Fin.append x y i) = (∑ i, p i*x i) + ∑ i, q i*y i := by
  rw [Fin.sum_univ_add]
  simp

lemma hannerProduct_eq_append_image {k l : ℕ} (A : Set (Fin k → ℝ)) (B : Set (Fin l → ℝ)) :
    hannerProduct A B = appendEquiv k l '' (A ×ˢ B) := by
  ext z
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    exact ⟨(x,y), ⟨hx,hy⟩, rfl⟩
  · rintro ⟨⟨x,y⟩, ⟨hx,hy⟩, rfl⟩
    exact ⟨x,hx,y,hy,rfl⟩

namespace RealNormData

lemma unit_coordMax {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (g.coordMax h).unit = hannerProduct g.unit h.unit := by
  rw [coordMax, unit_comap, unit_max, hannerProduct_eq_append_image]
  rfl

lemma unit_coordSum {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (g.coordSum h).unit = hannerJoin g.unit h.unit := by
  rw [coordSum, unit_comap, unit_sum, LinearEquiv.symm_symm]
  change (appendEquiv k l).toLinearMap '' convexHull ℝ _ = _
  rw [LinearMap.image_convexHull]
  simp only [hannerJoin, image_union, image_image]
  rfl

lemma volumeReal_unit_coordMax {k l : ℕ} (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (volume (g.coordMax h).unit).toReal = (volume g.unit).toReal * (volume h.unit).toReal := by
  rw [coordMax, unit_comap, LinearEquiv.symm_symm, volume_appendEquiv_image]
  exact g.measureReal_unit_max h volume volume

lemma volumeReal_unit_coordSum {k l : ℕ} (hk : 0 < k) (hl : 0 < l)
    (g : RealNormData (Fin k → ℝ)) (h : RealNormData (Fin l → ℝ)) :
    (volume (g.coordSum h).unit).toReal = (Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l) *
      (volume g.unit).toReal * (volume h.unit).toReal := by
  have : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp hk
  have : Nonempty (Fin l) := Fin.pos_iff_nonempty.mp hl
  rw [coordSum, unit_comap, LinearEquiv.symm_symm, volume_appendEquiv_image]
  change (((volume : Measure (Fin k → ℝ)).prod (volume : Measure (Fin l → ℝ)))
    (g.sum h).unit).toReal = _
  simpa only [Module.finrank_pi, Module.finrank_self, Fintype.card_fin, mul_one] using
    g.measureReal_unit_sum h volume volume

lemma unit_interval (a : ℝ) (ha : 0 < a) :
    (interval a ha).unit = Icc (fun _ : Fin 1 => -a) (fun _ => a) := by
  ext x
  simp only [unit, Set.mem_ofPred_eq, interval_apply, div_le_one ha, abs_le, mem_Icc,
    Pi.le_def, Fin.forall_fin_one]

lemma volumeReal_unit_interval (a : ℝ) (ha : 0 < a) :
    (volume (interval a ha).unit).toReal = 2*a := by
  rw [unit_interval, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_one, sub_neg_eq_add, ENNReal.toReal_ofReal (by linarith : 0 ≤ a+a)]
  ring

lemma IsDual.polar_unit {n : ℕ} {g h : RealNormData (Fin n → ℝ)} (hd : g.IsDual h) :
    coordinatePolar g.unit = h.unit := by
  ext p
  constructor
  · intro hp
    obtain ⟨x,hx,he⟩ := hd.2 p
    change h p ≤ 1
    rw [← he]
    exact hp x hx
  · intro hp x hx
    change h p ≤ 1 at hp
    exact (hd.1 x p).trans <|
      (mul_le_mul_of_nonneg_right hx (h.nonneg p)).trans (by simpa using hp)

lemma interval_isDual (a : ℝ) (ha : 0 < a) :
    (interval a ha).IsDual (interval a⁻¹ (inv_pos.mpr ha)) := by
  constructor
  · intro x p
    simp only [Fin.sum_univ_one, interval_apply, div_inv_eq_mul]
    calc
      p 0 * x 0 ≤ |p 0 * x 0| := le_abs_self _
      _ = |x 0| / a * (|p 0| * a) := by rw [abs_mul]; field_simp
  · intro p
    by_cases hp : 0 ≤ p 0
    · refine ⟨fun _ => a, ?_, ?_⟩
      · simp [unit, abs_of_pos ha, ne_of_gt ha]
      · simp [abs_of_nonneg hp]
    · refine ⟨fun _ => -a, ?_, ?_⟩
      · simp [unit, abs_of_pos ha, ne_of_gt ha]
      · simp [abs_of_neg (lt_of_not_ge hp)]

theorem IsDual.coordMax_sum {k l : ℕ} {g g' : RealNormData (Fin k → ℝ)}
    {h h' : RealNormData (Fin l → ℝ)} (hg : g.IsDual g') (hh : h.IsDual h') :
    (g.coordMax h).IsDual (g'.coordSum h') := by
  constructor
  · intro x p
    obtain ⟨⟨x₁,x₂⟩,rfl⟩ := (appendEquiv k l).surjective x
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    simp only [appendEquiv_apply, coordMax_append, coordSum_append, dot_append]
    calc
      _ ≤ g x₁ * g' p₁ + h x₂ * h' p₂ := add_le_add (hg.1 _ _) (hh.1 _ _)
      _ ≤ Max.max (g x₁) (h x₂) * g' p₁ + Max.max (g x₁) (h x₂) * h' p₂ :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (g'.nonneg _))
          (mul_le_mul_of_nonneg_right (le_max_right _ _) (h'.nonneg _))
      _ = _ := by ring
  · intro p
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    obtain ⟨x,hx,hxp⟩ := hg.2 p₁
    obtain ⟨y,hy,hyp⟩ := hh.2 p₂
    refine ⟨Fin.append x y, ?_, ?_⟩
    · simpa only [unit, Set.mem_ofPred_eq, coordMax_append, max_le_iff] using And.intro hx hy
    · simp only [appendEquiv_apply, dot_append, coordSum_append, hxp, hyp]

theorem IsDual.coordSum_max {k l : ℕ} {g g' : RealNormData (Fin k → ℝ)}
    {h h' : RealNormData (Fin l → ℝ)} (hg : g.IsDual g') (hh : h.IsDual h') :
    (g.coordSum h).IsDual (g'.coordMax h') := by
  constructor
  · intro x p
    obtain ⟨⟨x₁,x₂⟩,rfl⟩ := (appendEquiv k l).surjective x
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    simp only [appendEquiv_apply, coordMax_append, coordSum_append, dot_append]
    calc
      _ ≤ g x₁ * g' p₁ + h x₂ * h' p₂ := add_le_add (hg.1 _ _) (hh.1 _ _)
      _ ≤ g x₁ * Max.max (g' p₁) (h' p₂) + h x₂ * Max.max (g' p₁) (h' p₂) :=
        add_le_add (mul_le_mul_of_nonneg_left (le_max_left _ _) (g.nonneg _))
          (mul_le_mul_of_nonneg_left (le_max_right _ _) (h.nonneg _))
      _ = _ := by ring
  · intro p
    obtain ⟨⟨p₁,p₂⟩,rfl⟩ := (appendEquiv k l).surjective p
    obtain ⟨x,hx,hxp⟩ := hg.2 p₁
    obtain ⟨y,hy,hyp⟩ := hh.2 p₂
    rcases le_total (h' p₂) (g' p₁) with hp | hp
    · refine ⟨Fin.append x 0, ?_, ?_⟩
      · simpa only [unit, Set.mem_ofPred_eq, coordSum_append, apply_zero, add_zero] using hx
      · simp only [appendEquiv_apply, dot_append, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          add_zero, hxp, coordMax_append, max_eq_left hp]
    · refine ⟨Fin.append 0 y, ?_, ?_⟩
      · simpa only [unit, Set.mem_ofPred_eq, coordSum_append, apply_zero, zero_add] using hy
      · simp only [appendEquiv_apply, dot_append, Pi.zero_apply, mul_zero, Finset.sum_const_zero,
          zero_add, hyp, coordMax_append, max_eq_right hp]

end RealNormData

lemma IsHanner.dim_pos {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) : 0 < n := by
  induction hK with
  | interval a ha => omega
  | product hA hB ihA ihB => omega
  | join hA hB ihA ihB => omega

lemma hanner_volume_recursion {k l : ℕ} {v v' w w' : ℝ}
    (h₁ : v*v' = (4:ℝ)^k / Nat.factorial k)
    (h₂ : w*w' = (4:ℝ)^l / Nat.factorial l) :
    (v*w) * ((Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l) * v' * w') =
      (4:ℝ)^(k+l) / Nat.factorial (k+l) := by
  calc
    _ = ((Nat.factorial k : ℝ) * Nat.factorial l / Nat.factorial (k+l)) * (v*v') * (w*w') := by ring
    _ = _ := by
      rw [h₁, h₂, pow_add]
      have hfk : (Nat.factorial k : ℝ) ≠ 0 := by positivity
      have hfl : (Nat.factorial l : ℝ) ≠ 0 := by positivity
      field_simp

theorem IsHanner.gauges {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) :
    ∃ g h : RealNormData (Fin n → ℝ), K = g.unit ∧ g.IsDual h ∧ IsHanner h.unit ∧
      (volume g.unit).toReal * (volume h.unit).toReal = (4:ℝ)^n / Nat.factorial n := by
  induction hK with
  | interval a ha =>
    refine ⟨.interval a ha, .interval a⁻¹ (inv_pos.mpr ha), ?_,
      RealNormData.interval_isDual a ha, ?_, ?_⟩
    · exact (RealNormData.unit_interval a ha).symm
    · rw [RealNormData.unit_interval]
      exact IsHanner.interval a⁻¹ (inv_pos.mpr ha)
    · rw [RealNormData.volumeReal_unit_interval, RealNormData.volumeReal_unit_interval]
      norm_num
      field_simp
      norm_num
  | @product k l A B hA hB ihA ihB =>
    obtain ⟨g,g',hAg,hgd,hgH,hgv⟩ := ihA
    obtain ⟨h,h',hBh,hhd,hhH,hhv⟩ := ihB
    refine ⟨g.coordMax h, g'.coordSum h', ?_, hgd.coordMax_sum hhd, ?_, ?_⟩
    · rw [RealNormData.unit_coordMax, hAg, hBh]
    · rw [RealNormData.unit_coordSum]
      exact IsHanner.join hgH hhH
    · rw [RealNormData.volumeReal_unit_coordMax,
        RealNormData.volumeReal_unit_coordSum hA.dim_pos hB.dim_pos]
      exact hanner_volume_recursion hgv hhv
  | @join k l A B hA hB ihA ihB =>
    obtain ⟨g,g',hAg,hgd,hgH,hgv⟩ := ihA
    obtain ⟨h,h',hBh,hhd,hhH,hhv⟩ := ihB
    refine ⟨g.coordSum h, g'.coordMax h', ?_, hgd.coordSum_max hhd, ?_, ?_⟩
    · rw [RealNormData.unit_coordSum, hAg, hBh]
    · rw [RealNormData.unit_coordMax]
      exact IsHanner.product hgH hhH
    · rw [RealNormData.volumeReal_unit_coordSum hA.dim_pos hB.dim_pos,
        RealNormData.volumeReal_unit_coordMax, mul_comm]
      exact hanner_volume_recursion (by simpa only [mul_comm] using hgv)
        (by simpa only [mul_comm] using hhv)

theorem IsHanner.polar {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) :
    IsHanner (coordinatePolar K) := by
  obtain ⟨g,h,rfl,hd,hH,-⟩ := hK.gauges
  rwa [hd.polar_unit]

theorem IsHanner.volumeProduct {n : ℕ} {K : Set (Fin n → ℝ)} (hK : IsHanner K) :
    (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n / Nat.factorial n := by
  obtain ⟨g,h,rfl,hd,-,hv⟩ := hK.gauges
  rwa [hd.polar_unit]

lemma coordinateTranspose_apply {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (p x : Fin n → ℝ) :
    (∑ i, coordinateTranspose T p i * x i) = ∑ i, p i * T x i := by
  change (Matrix.toLin' (LinearMap.toMatrix' T.toLinearMap).transpose p) ⬝ᵥ x =
    p ⬝ᵥ T.toLinearMap x
  rw [Matrix.toLin'_apply, dotProduct_comm]
  rw [Matrix.dotProduct_transpose_mulVec]
  rw [← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']

lemma det_coordinateTranspose {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) :
    LinearMap.det (coordinateTranspose T).toLinearMap = LinearMap.det T.toLinearMap :=
  det_coordinateTransposeMap _

lemma coordinatePolar_image {n : ℕ} (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ))
    (K : Set (Fin n → ℝ)) :
    coordinatePolar (T '' K) = coordinateTranspose T ⁻¹' coordinatePolar K := by
  ext p
  simp only [coordinatePolar, Set.mem_ofPred_eq, mem_preimage, forall_mem_image,
    coordinateTranspose_apply]

theorem volumeProduct_linear_image {n : ℕ}
    (T : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)) (K : Set (Fin n → ℝ)) :
    (volume (T '' K)).toReal * (volume (coordinatePolar (T '' K))).toReal =
      (volume K).toReal * (volume (coordinatePolar K)).toReal := by
  rw [coordinatePolar_image]
  have hi := Measure.addHaar_image_linearMap volume T.toLinearMap K
  change volume (T '' K) = _ at hi
  rw [hi, Measure.addHaar_preimage_linearEquiv, LinearEquiv.det_coe_symm,
    det_coordinateTranspose, abs_inv, ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_ofReal (inv_nonneg.mpr (abs_nonneg _))]
  have hd : |LinearMap.det T.toLinearMap| ≠ 0 := abs_ne_zero.mpr T.isUnit_det'.ne_zero
  field_simp

theorem IsLinearHanner.volumeProduct {n : ℕ} {K : Set (Fin n → ℝ)}
    (hK : IsLinearHanner K) :
    (volume K).toReal * (volume (coordinatePolar K)).toReal = (4:ℝ)^n / Nat.factorial n := by
  obtain ⟨H,hH,T,rfl⟩ := hK
  rw [volumeProduct_linear_image]
  exact hH.volumeProduct

open Set Metric MeasureTheory
open scoped Topology Pointwise
namespace RealNormData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [inst443 : FiniteDimensional ℝ E]

omit inst443 in
lemma unit_eq_image_closedBall [FiniteDimensional ℝ E] (g : RealNormData E) :
    g.unit = g.spaceEquiv '' closedBall (0:g.Space) 1 := by
  ext x
  constructor
  · intro hx
    exact ⟨g.spaceEquiv.symm x, by simpa only [mem_closedBall_zero_iff,space_norm,LinearEquiv.apply_symm_apply,unit,Set.mem_ofPred_eq] using hx, g.spaceEquiv.apply_symm_apply x⟩
  · rintro ⟨y,hy,rfl⟩
    simpa only [mem_closedBall_zero_iff,space_norm,unit,Set.mem_ofPred_eq] using hy

end RealNormData

open Set Finset MeasureTheory

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Medians
attribute [-instance] _root_.Convexity.StdSimplex.instInhabited _root_.Convexity.StdSimplex.instNonempty _root_.Convexity.StdSimplex.instSubsingleton _root_.Convexity.StdSimplex.instUnique _root_.Convexity.StdSimplex.topologicalSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

section
open Set Metric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extreme_unit_norm_add {x u : E}
    (hx : x ∈ (closedBall (0 : E) 1).extremePoints ℝ) (hnx : ‖x‖ = 1)
    (hadd : ‖u‖ + ‖x - u‖ = 1) : u = ‖u‖ • x := by
  by_cases hu : ‖u‖ = 0
  · have hu0 : u = 0 := norm_eq_zero.mp hu
    simp [hu0]
  by_cases hv : ‖x - u‖ = 0
  · have hv0 : x = u := sub_eq_zero.mp (norm_eq_zero.mp hv)
    simp [← hv0, hnx]
  have hup : 0 < ‖u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hu)
  have hvp : 0 < ‖x-u‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hv)
  have hnu : ‖u‖⁻¹ • u ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hup), inv_mul_cancel₀ hu]
  have hnv : ‖x-u‖⁻¹ • (x-u) ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hvp), inv_mul_cancel₀ hv]
  have hseg : x ∈ openSegment ℝ (‖u‖⁻¹ • u) (‖x-u‖⁻¹ • (x-u)) := by
    refine ⟨‖u‖, ‖x-u‖, hup, hvp, hadd, ?_⟩
    simp only [smul_smul, mul_inv_cancel₀ hu, mul_inv_cancel₀ hv, one_smul]
    abel
  have heq : ‖u‖⁻¹ • u = x := hx.2 hnu hnv hseg
  calc
    u = ‖u‖ • (‖u‖⁻¹ • u) := by rw [smul_smul, mul_inv_cancel₀ hu, one_smul]
    _ = ‖u‖ • x := by rw [heq]

theorem dist_extreme_unit_eq_two [Nontrivial E] (hmed : HasMetricMedians E)
    {x y : E} (hx : x ∈ (closedBall (0 : E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0 : E) 1).extremePoints ℝ) (hxy : x ≠ y) :
    dist x y = 2 := by
  have hnx : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere hx)
  have hny : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere hy)
  obtain ⟨m, hm⟩ := hmed ![0, x, y]
  have hmx : ‖m‖ + ‖x-m‖ = 1 := by
    have h := hm 0 1 (by decide)
    simpa [dist_eq_norm, norm_sub_rev, hnx] using h.symm
  have hmy : ‖m‖ + ‖y-m‖ = 1 := by
    have h := hm 0 2 (by decide)
    simpa [dist_eq_norm, norm_sub_rev, hny] using h.symm
  have hm0 : m = 0 := by
    by_contra hm0
    have h1 := extreme_unit_norm_add hx hnx hmx
    have h2 := extreme_unit_norm_add hy hny hmy
    have hn : ‖m‖ ≠ 0 := norm_ne_zero_iff.mpr hm0
    apply hxy
    have hh := congrArg (fun z : E => ‖m‖⁻¹ • z) (h1.symm.trans h2)
    simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hh
  have h := hm 1 2 (by decide)
  change dist x y = dist x m + dist m y at h
  norm_num [hm0, hnx, hny, dist_zero_left, dist_zero_right] at h ⊢
  exact h

theorem finite_extreme_unit_of_medians [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) :
    ((closedBall (0 : E) 1).extremePoints ℝ).Finite := by
  have htb : TotallyBounded ((closedBall (0 : E) 1).extremePoints ℝ) :=
    (isCompact_closedBall (0 : E) 1).totallyBounded.subset extremePoints_subset
  obtain ⟨t, ht, htfin, hcover⟩ := Metric.finite_approx_of_totallyBounded htb 1 zero_lt_one
  apply htfin.subset
  intro x hx
  obtain ⟨y, hyt, hxyball⟩ := mem_iUnion₂.mp (hcover hx)
  have heq : x = y := by
    by_contra hne
    have hd := dist_extreme_unit_eq_two hmed hx (ht hyt) hne
    have hb : dist x y < 1 := hxyball
    linarith
  exact heq ▸ hyt

theorem unitBall_eq_finite_convexHull_of_medians [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) :
    ∃ V : Set E, V.Finite ∧ closedBall (0 : E) 1 = convexHull ℝ V := by
  let V := (closedBall (0 : E) 1).extremePoints ℝ
  have hV : V.Finite := finite_extreme_unit_of_medians hmed
  refine ⟨V, hV, ?_⟩
  have h := closure_convexHull_extremePoints (isCompact_closedBall (0 : E) 1)
    (convex_closedBall (0 : E) 1)
  change closure (convexHull ℝ V) = closedBall (0 : E) 1 at h
  rw [(hV.isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm

end

section
open Set Metric
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [inst449 : NormedSpace ℝ E]

lemma exists_unitBall_dual_maximizer [FiniteDimensional ℝ E] (f : E →L[ℝ] ℝ) :
    ∃ v : E, ‖v‖ ≤ 1 ∧ f v = ‖f‖ := by
  obtain ⟨v, hv, hmax⟩ := (isCompact_closedBall (0 : E) 1).exists_isMaxOn
    (nonempty_closedBall.mpr (by norm_num)) f.continuous.continuousOn
  have hvnorm : ‖v‖ ≤ 1 := by simpa using hv
  have hfv : 0 ≤ f v := by
    have := hmax (by simp : (0 : E) ∈ closedBall 0 1)
    simpa using this
  have hupper (x : E) : f x ≤ f v * ‖x‖ := by
    by_cases hx : x = 0
    · simp [hx]
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hunit : ‖(‖x‖⁻¹ : ℝ) • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hnx.le),
        inv_mul_cancel₀ hnx.ne']
    have hh := hmax (by simpa using hunit)
    have hh' : ‖x‖⁻¹ * f x ≤ f v := by simpa using hh
    have := mul_le_mul_of_nonneg_left hh' hnx.le
    simpa [← mul_assoc, hnx.ne', mul_comm] using this
  have hop : ‖f‖ ≤ f v := by
    apply f.opNorm_le_bound hfv
    intro x
    rw [Real.norm_eq_abs, abs_le]
    have hneg := hupper (-x)
    simp only [map_neg, norm_neg] at hneg
    exact ⟨by linarith, hupper x⟩
  refine ⟨v, hvnorm, le_antisymm ?_ hop⟩
  calc
    f v ≤ ‖f v‖ := le_abs_self _
    _ ≤ ‖f‖ * ‖v‖ := f.le_opNorm v
    _ ≤ ‖f‖ := by simpa using mul_le_mul_of_nonneg_left hvnorm (norm_nonneg f)

end

section
open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extreme_unit_scaled_norm_add {e u : E} {R : ℝ}
    (he : e ∈ (closedBall (0 : E) 1).extremePoints ℝ) (hne : ‖e‖ = 1)
    (hR : 0 < R) (hadd : ‖u‖ + ‖R • e - u‖ = R) : u = ‖u‖ • e := by
  have hden : ‖R⁻¹ • u‖ + ‖e - R⁻¹ • u‖ = 1 := by
    have hi : e - R⁻¹ • u = R⁻¹ • (R • e - u) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hR.ne', one_smul]
    rw [hi, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR),
      ← mul_add, hadd, inv_mul_cancel₀ hR.ne']
  have h := extreme_unit_norm_add he hne hden
  have hh := congrArg (fun z : E => R • z) h
  simpa only [smul_smul, mul_inv_cancel₀ hR.ne', one_smul, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR), ← mul_assoc, one_mul] using hh

theorem extreme_unit_spear [Nontrivial E] (hmed : HasMetricMedians E)
    {e : E} (he : e ∈ (closedBall (0 : E) 1).extremePoints ℝ) (x : E) :
    max ‖x + e‖ ‖x - e‖ = ‖x‖ + 1 := by
  have hne : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere he)
  obtain ⟨m,hm⟩ := hmed ![0, (2:ℝ) • e, x+e]
  have h2 : ‖m‖ + ‖(2:ℝ) • e-m‖ = 2 := by
    have hh := hm 0 1 (by decide)
    simpa [dist_eq_norm, norm_sub_rev, norm_smul, hne] using hh.symm
  have hmx := extreme_unit_scaled_norm_add he hne (by norm_num : (0:ℝ)<2) h2
  have hxm : ‖x+e‖ = ‖m‖ + ‖x+e-m‖ := by
    have hh := hm 0 2 (by decide)
    change dist 0 (x+e) = dist 0 m + dist m (x+e) at hh
    simpa only [dist_eq_norm, zero_sub, norm_neg, norm_sub_rev m (x+e)] using hh
  have hym : ‖x-e‖ = 2 - ‖m‖ + ‖x+e-m‖ := by
    have hh := hm 1 2 (by decide)
    change dist ((2:ℝ) • e) (x+e) = dist ((2:ℝ) • e) m + dist m (x+e) at hh
    have heq : (2:ℝ) • e - (x+e) = -(x-e) := by module
    simp only [dist_eq_norm, heq, norm_neg, norm_sub_rev m (x+e)] at hh
    linarith
  have hbound : ‖x‖ ≤ |‖m‖-1| + ‖x+e-m‖ := by
    have heq : (‖m‖-1) • e = m-e := by rw [sub_smul, one_smul, ← hmx]
    calc
      ‖x‖ = ‖(‖m‖-1) • e + (x+e-m)‖ := by rw [heq]; congr 1; abel
      _ ≤ ‖(‖m‖-1) • e‖ + ‖x+e-m‖ := norm_add_le _ _
      _ = _ := by rw [norm_smul, Real.norm_eq_abs, hne, mul_one]
  apply le_antisymm
  · exact max_le (by simpa [hne] using norm_add_le x e)
      (by simpa [hne] using norm_sub_le x e)
  · rcases le_total 1 ‖m‖ with ht | ht
    · rw [abs_of_nonneg (by linarith)] at hbound
      exact (by linarith : ‖x‖+1 ≤ ‖x+e‖).trans (le_max_left _ _)
    · rw [abs_of_nonpos (by linarith)] at hbound
      exact (by linarith : ‖x‖+1 ≤ ‖x-e‖).trans (le_max_right _ _)

lemma dual_eval_le_unit_norm (f : E →L[ℝ] ℝ) (hf : ‖f‖ ≤ 1) (x : E) : f x ≤ ‖x‖ := by
  calc
    f x ≤ |f x| := le_abs_self _
    _ ≤ ‖f‖ * ‖x‖ := f.le_opNorm x
    _ ≤ ‖x‖ := by simpa using mul_le_mul_of_nonneg_right hf (norm_nonneg x)

theorem extreme_unit_dual_face_norming [Nontrivial E] (hmed : HasMetricMedians E)
    {e : E} (he : e ∈ (closedBall (0 : E) 1).extremePoints ℝ) (x : E) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ f x = ‖x‖ ∧ (f e = 1 ∨ f e = -1) := by
  have hne : ‖e‖ = 1 := mem_sphere_zero_iff_norm.mp
    (extremePoints_closedBall_subset_sphere he)
  have hs := extreme_unit_spear hmed he x
  rcases le_total ‖x-e‖ ‖x+e‖ with hle | hle
  · rw [max_eq_left hle] at hs
    obtain ⟨f,hfn,hf⟩ := exists_dual_vector'' ℝ (x+e)
    have hx := dual_eval_le_unit_norm f hfn x
    have he' := dual_eval_le_unit_norm f hfn e
    rw [map_add, hs] at hf
    change f x + f e = ‖x‖ + 1 at hf
    rw [hne] at he'
    exact ⟨f,hfn,by linarith,Or.inl (by linarith)⟩
  · rw [max_eq_right hle] at hs
    obtain ⟨f,hfn,hf⟩ := exists_dual_vector'' ℝ (x-e)
    have hx := dual_eval_le_unit_norm f hfn x
    have he' := dual_eval_le_unit_norm f hfn (-e)
    rw [map_sub, hs] at hf
    change f x - f e = ‖x‖ + 1 at hf
    rw [map_neg, norm_neg, hne] at he'
    exact ⟨f,hfn,by linarith,Or.inr (by linarith)⟩

end

open Set Metric

end SymmetricMahler
end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.StdSimplexCompat
attribute [-instance] _root_.OAI.Mahler.finiteDimensional_continuousAlternatingMap _root_.OAI.isProbabilityMeasure_map_fst _root_.OAI.isProbabilityMeasure_map_measurableEquiv _root_.OAI.isProbabilityMeasure_map_snd _root_.OAI.isProbabilityMeasure_map_subtype_val
/-!
# Standard simplex compatibility layer for ports of openai/math

This file is not OpenAI's code. OpenAI's openai/math is built on Mathlib `d13f23b`; prove2.me's
environment is Mathlib `0df444a`. Both have the structure `Convexity.StdSimplex`, but `0df444a`
lacks part of its API (the files `Mathlib.Geometry.Convex.ConvexSpace.{Topology,
CompactSpaceStdSimplex, Barycenter, PathConnectedSpaceStdSimplex}` and some lemmas of `Defs`),
and its `SimplexCategory.toTop` takes the topological simplex to be the subtype
`stdSimplex ℝ (Fin (n+1))`, where `d13f23b` takes the structure.

Part 1 adds the missing `d13f23b` API to `Convexity.StdSimplex` under its `d13f23b` names. It is
copied from Mathlib `d13f23b` (Copyright (c) 2025 Lean FRO, LLC, authors Kim Morrison, Andrew
Yang, Yaël Dillies; Copyright (c) 2026 Joël Riou; released under the Apache 2.0 license), adapted
to `0df444a` (module keywords removed).

Part 2 (`OAI.SStd`) is ours: the subtype `stdSimplex R X` on a finite type with the `d13f23b`
names, for ported code that identifies the simplex with `SimplexCategory.toTop.obj`; there the
port rewrites `Convexity.StdSimplex` to `OAI.SStd`.
-/

noncomputable section StdSimplexCompat

universe u v w

open Topology

/-! ## Part 1: the `d13f23b` API missing from `0df444a`, on `Convexity.StdSimplex` -/

namespace Convexity

namespace StdSimplex

section Semiring

variable {R : Type u} [PartialOrder R] [Semiring R] {X Y Z : Type*}

lemma range_toFun_comp_weights [Fintype X] :
    Set.range (fun t ↦ t.weights : StdSimplex R X → (X → R)) =
    (⋂ (i : X), { s | 0 ≤ s i }) ∩ { s | ∑ i, s i = 1 } := by
  ext s
  simp only [Set.mem_range, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
  refine ⟨?_, ?_⟩
  · rintro ⟨s, rfl⟩
    exact ⟨s.weights_nonneg, by simp⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨{
      weights := Finsupp.equivFunOnFinite.symm s
      nonneg m := by simpa using h₁ m
      total := by simpa [Finsupp.sum_fintype] }, by simp⟩

variable [IsStrictOrderedRing R]

lemma map_id' : map (R := R) (id : X → X) = id := by
  funext f
  exact map_id f

end Semiring

end StdSimplex

/-! ### Topology (Mathlib `d13f23b`, `Geometry/Convex/ConvexSpace/Topology.lean`) -/

namespace StdSimplex

variable (R : Type u) [PartialOrder R] [Ring R] [TopologicalSpace R]

namespace topologicalSpaceInduced

attribute [local instance] topologicalSpaceInduced

lemma continuous_iff {T ι : Type*} [TopologicalSpace T] (f : T → StdSimplex R ι) :
    Continuous f ↔ ∀ (i : ι), Continuous (fun t ↦ (f t).weights i) := by
  rw [continuous_induced_rng]
  exact continuous_pi_iff

lemma continuous_map [IsStrictOrderedRing R] [IsTopologicalRing R]
    {ι₁ ι₂ : Type*} [Finite ι₁] (f : ι₁ → ι₂) :
    Continuous (map (R := R) f) := by
  rw [continuous_iff]
  fun_prop

end topologicalSpaceInduced

variable [IsStrictOrderedRing R] [IsTopologicalRing R]

lemma topologicalSpace_eq (M : Type v) [Finite M] :
    topologicalSpace R M = topologicalSpaceInduced _ _ := by
  refine le_antisymm ?_ ?_
  · exact iSup_le (fun ι ↦ iSup_le (fun _ ↦ iSup_le
      (fun f ↦ (topologicalSpaceInduced.continuous_map R f).coinduced_le)))
  · refine le_trans ?_ (le_iSup _ M)
    refine le_trans ?_ (le_iSup _ (by assumption))
    refine le_trans ?_ (le_iSup _ id)
    rw [map_id']
    rfl

lemma isEmbedding_toFun_comp_weights (M : Type*) [Finite M] :
    IsEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  eq_induced := by rw [topologicalSpace_eq]
  injective _ _ h := by ext; apply congr_fun h

lemma isClosedEmbedding_toFun_comp_weights
    [OrderClosedTopology R] (M : Type*) [Finite M] :
    IsClosedEmbedding (fun t ↦ t.weights : StdSimplex R M → M → R) where
  toIsEmbedding := isEmbedding_toFun_comp_weights R M
  isClosed_range := by
    have := Fintype.ofFinite M
    rw [range_toFun_comp_weights]
    refine IsClosed.inter (isClosed_iInter (fun _ ↦ isClosed_le ?_ ?_))
      (isClosed_eq ?_ ?_)
    all_goals fun_prop

end StdSimplex

/-! ### Compactness (Mathlib `d13f23b`, `CompactSpaceStdSimplex.lean`) -/

namespace StdSimplex

instance compactSpace (R M : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R]
    [PartialOrder R] [IsStrictOrderedRing R] [CompactIccSpace R] [OrderClosedTopology R]
    [Finite M] :
    CompactSpace (StdSimplex R M) where
  isCompact_univ := by
    rw [(isEmbedding_toFun_comp_weights R M).isCompact_iff, Set.image_univ]
    refine IsCompact.of_isClosed_subset (s := Set.Icc 0 1) isCompact_Icc
      (isClosedEmbedding_toFun_comp_weights R M).isClosed_range ?_
    rintro _ ⟨x, rfl⟩
    exact ⟨fun i => x.weights_nonneg i, fun i => x.weights_apply_le_one i⟩

end StdSimplex

/-! ### Barycenters (Mathlib `d13f23b`, `Barycenter.lean`) -/

/-! ### Path-connectedness (Mathlib `d13f23b`, `PathConnectedSpaceStdSimplex.lean`) -/

end Convexity

/-! ## Part 2: `OAI.SStd`, the subtype `stdSimplex R X` with the `d13f23b` names -/

end StdSimplexCompat
end

section
-- module Solutions.OAIQ2_Mah.Mahler_EqualityMedians
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Filter Finset Metric
open scoped Topology

lemma isCompact_convexHull_of_isCompact {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {S : Set E} (hS : IsCompact S) : IsCompact (convexHull ℝ S) := by
  classical
  let D := Module.finrank ℝ E + 1
  let T (k : ℕ) : Set ((Fin k → ℝ) × (Fin k → E)) :=
    {weights : Fin k → ℝ | (∀ index, 0 ≤ weights index) ∧ ∑ index, weights index = 1} ×ˢ
      Set.pi Set.univ (fun _ => S)
  let f (k : ℕ) (p : (Fin k → ℝ) × (Fin k → E)) := ∑ i, p.1 i • p.2 i
  have hWeights (k : ℕ) :
      IsCompact {weights : Fin k → ℝ | (∀ index, 0 ≤ weights index) ∧
        ∑ index, weights index = 1} := by
    have compact := isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ (Fin k)).continuous
    rw [Convexity.StdSimplex.range_toFun_comp_weights] at compact
    simpa only [Set.iInter_ofPred, Set.ofPred_inter_eq_sep, Set.mem_ofPred_eq,
      and_comm] using compact
  have hT (k : ℕ) : IsCompact (T k) :=
    (hWeights k).prod (by
      convert (isCompact_pi_infinite (ι := Fin k) (fun _ => hS)) using 1
      ext x
      simp only [Set.mem_pi, Set.mem_univ, forall_const, Set.mem_ofPred_eq])
  have hf (k : ℕ) : Continuous (f k) := by unfold f; fun_prop
  have he : convexHull ℝ S = ⋃ k : Fin (D+1), f k '' T k := by
    apply subset_antisymm
    · intro x hx
      obtain ⟨ι,_,z,w,hz,hind,hw,hs,hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      let e := Fintype.equivFin ι
      have hk : Fintype.card ι < D+1 := by
        have hh := hind.card_le_finrank_succ
        have hb := Submodule.finrank_le (vectorSpan ℝ (Set.range z))
        dsimp [D]
        omega
      apply Set.mem_iUnion.mpr
      refine ⟨⟨Fintype.card ι,hk⟩, (w ∘ e.symm,z ∘ e.symm), ?_, ?_⟩
      · refine ⟨⟨fun i => (hw (e.symm i)).le, ?_⟩, ?_⟩
        · simpa only [Function.comp_apply, Equiv.sum_comp] using hs
        · intro i hi
          exact hz (mem_range_self _)
      · dsimp only [f,Function.comp_apply]
        exact (e.symm.sum_comp (fun i => w i • z i)).trans hx
    · intro x hx
      obtain ⟨k,p, hp, rfl⟩ := Set.mem_iUnion.mp hx
      exact mem_convexHull_of_exists_fintype p.1 p.2 hp.1.1 hp.1.2
        (fun i => hp.2 i (Set.mem_univ i)) rfl
  rw [he]
  exact isCompact_iUnion (fun k => (hT k).image (hf k))

open Set Filter Finset Metric Complex
open scoped Topology
open MahlerConformal

open Set Filter Finset Metric Complex MeasureTheory
open scoped Topology
open MahlerConformal

open Set Finset MeasureTheory
open MahlerConformal

open Set MeasureTheory Metric

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Faces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Metric
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace IsFace
variable {K F G : Set E}
lemma subset (h : IsFace K F) : F ⊆ K := h.2.subset
lemma trans (h : IsFace K F) (h' : IsFace F G) : IsFace K G :=
  ⟨h'.1, h.2.trans h'.2⟩
lemma inter (h : IsFace K F) (h' : IsFace K G) : IsFace K (F ∩ G) :=
  ⟨h.1.inter h'.1, h.2.inter h'.2⟩
lemma mono (h : IsFace K G) (hFK : F ⊆ K) (hGF : G ⊆ F) : IsFace F G :=
  ⟨h.1, h.2.mono hFK hGF⟩
lemma refl (h : Convex ℝ K) : IsFace K K := ⟨h, .rfl⟩
lemma empty (K : Set E) : IsFace K ∅ :=
  ⟨convex_empty, ⟨empty_subset _, fun _ _ _ _ _ h => h.elim⟩⟩

lemma eq_convexHull_inter {A : Set E} (h : IsFace (convexHull ℝ A) F) :
    F = convexHull ℝ (A ∩ F) := by
  apply subset_antisymm
  · let T : Set E := {x | x ∈ convexHull ℝ A ∧
        (x ∈ F → x ∈ convexHull ℝ (A ∩ F))}
    have hT : Convex ℝ T := by
      apply convex_iff_openSegment_subset.mpr
      intro x hx y hy z hz
      refine ⟨(convex_convexHull ℝ A).openSegment_subset hx.1 hy.1 hz, ?_⟩
      intro hzF
      exact (convex_convexHull ℝ (A ∩ F)).openSegment_subset
        (hx.2 (h.2.left_mem_of_mem_openSegment hx.1 hy.1 hzF hz))
        (hy.2 (h.2.right_mem_of_mem_openSegment hx.1 hy.1 hzF hz)) hz
    have hAT : A ⊆ T := fun x hx =>
      ⟨subset_convexHull ℝ A hx, fun hxF => subset_convexHull ℝ (A ∩ F) ⟨hx,hxF⟩⟩
    intro x hx
    exact (convexHull_min hAT hT (h.subset hx)).2 hx
  · exact convexHull_min inter_subset_right h.1

lemma isCompact_of_finite_hull {A : Set E} (hA : A.Finite)
    (h : IsFace (convexHull ℝ A) F) : IsCompact F := by
  rw [h.eq_convexHull_inter]
  exact (hA.inter_of_left F).isCompact_convexHull ℝ

lemma eq_of_inter_eq {A : Set E} (h : IsFace (convexHull ℝ A) F)
    (h' : IsFace (convexHull ℝ A) G) (he : A ∩ F = A ∩ G) : F = G := by
  rw [h.eq_convexHull_inter, h'.eq_convexHull_inter, he]
end IsFace

lemma subset_faceHull {K A : Set E} : A ⊆ faceHull K A :=
  fun _ hx => mem_sInter.mpr fun _ hF => hF.2 hx

lemma faceHull_min {K A F : Set E} (hF : IsFace K F) (hAF : A ⊆ F) :
    faceHull K A ⊆ F := sInter_subset_of_mem ⟨hF,hAF⟩

lemma isFace_faceHull {K A : Set E} (hK : Convex ℝ K) (hAK : A ⊆ K) :
    IsFace K (faceHull K A) := by
  refine ⟨convex_sInter (fun F hF => hF.1.1), ?_⟩
  exact isExtreme_sInter ⟨K,IsFace.refl hK,hAK⟩ (fun F hF => hF.1.2)

lemma faceHull_mono {K A B : Set E} (hAB : A ⊆ B) :
    faceHull K A ⊆ faceHull K B := by
  intro x hx
  exact mem_sInter.mpr fun F hF => mem_sInter.mp hx F ⟨hF.1,hAB.trans hF.2⟩

lemma finite_faces_of_finite_hull {A : Set E} (hA : A.Finite) :
    {F : Set E | IsFace (convexHull ℝ A) F}.Finite := by
  classical
  apply Set.Finite.of_finite_image (f := fun F : Set E => A ∩ F)
  · exact hA.finite_subsets.subset (by
      rintro _ ⟨F,-,rfl⟩
      exact inter_subset_left)
  · intro F hF G hG he
    exact hF.eq_of_inter_eq hG he

lemma finite_unit_faces_of_medians [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) :
    {F : Set E | IsFace (closedBall (0:E) 1) F}.Finite := by
  obtain ⟨V,hV,hB⟩ := unitBall_eq_finite_convexHull_of_medians hmed
  rw [hB]
  exact finite_faces_of_finite_hull hV

end

open Set Metric
open scoped Pointwise
section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma extreme_set_eq_ball_of_zero {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F) (h0 : (0:E) ∈ F) :
    F = closedBall (0:E) 1 := by
  apply subset_antisymm hF.subset
  intro x hx
  apply hF.left_mem_of_mem_openSegment hx (show -x ∈ closedBall (0:E) 1 by simpa using hx) h0
  refine ⟨(1:ℝ)/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
  simp

lemma norm_eq_one_of_mem_proper_face {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F) (hproper : F ≠ closedBall (0:E) 1)
    {x : E} (hx : x ∈ F) : ‖x‖ = 1 := by
  have hle : ‖x‖ ≤ 1 := mem_closedBall_zero_iff.mp (hF.subset hx)
  by_contra hne
  have hlt := lt_of_le_of_ne hle hne
  have h0 : (0:E) ∈ F := by
    by_cases hx0 : x = 0
    · simpa only [hx0] using hx
    have hpos := norm_pos_iff.mpr hx0
    have hxu : ‖x‖⁻¹ • x ∈ closedBall (0:E) 1 := by
      simp only [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hpos),inv_mul_cancel₀ hpos.ne',le_refl]
    apply hF.left_mem_of_mem_openSegment (show (0:E) ∈ closedBall (0:E) 1 by simp) hxu hx
    refine ⟨1-‖x‖,‖x‖,by linarith,hpos,by ring,?_⟩
    simp only [smul_zero,zero_add,smul_smul,mul_inv_cancel₀ hpos.ne',one_smul]
  exact hproper (extreme_set_eq_ball_of_zero hF h0)

lemma normalized_summand_mem_face {F : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F) {x m : E}
    (hx : x ∈ F) (hnx : ‖x‖ = 1) (hm : m ≠ 0)
    (hadd : ‖m‖+‖x-m‖ = 1) : ‖m‖⁻¹ • m ∈ F := by
  have hmp := norm_pos_iff.mpr hm
  by_cases hxm : x = m
  · simpa [← hxm,hnx] using hx
  have hxp : 0 < ‖x-m‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxm)
  apply hF.left_mem_of_mem_openSegment (show ‖m‖⁻¹ • m ∈ closedBall (0:E) 1 by
    simp [norm_smul,hmp.ne'])
    (show ‖x-m‖⁻¹ • (x-m) ∈ closedBall (0:E) 1 by
      simp [norm_smul,hxp.ne']) hx
  refine ⟨‖m‖,‖x-m‖,hmp,hxp,hadd,?_⟩
  simp only [smul_smul,mul_inv_cancel₀ hmp.ne',mul_inv_cancel₀ hxp.ne',one_smul]
  abel

theorem disjoint_faces_distance_two (hmed : HasMetricMedians E)
    {F G : Set E} (hF : IsExtreme ℝ (closedBall (0:E) 1) F)
    (hG : IsExtreme ℝ (closedBall (0:E) 1) G)
    (hdis : Disjoint F G) {x y : E} (hx : x ∈ F) (hy : y ∈ G) :
    dist x y = 2 := by
  have hFp : F ≠ closedBall (0:E) 1 := by
    intro he; exact Set.disjoint_left.mp hdis (he ▸ hG.subset hy) hy
  have hGp : G ≠ closedBall (0:E) 1 := by
    intro he; exact Set.disjoint_left.mp hdis hx (he ▸ hF.subset hx)
  have hnx := norm_eq_one_of_mem_proper_face hF hFp hx
  have hny := norm_eq_one_of_mem_proper_face hG hGp hy
  obtain ⟨m,hm⟩ := hmed ![0,x,y]
  have hmx : ‖m‖+‖x-m‖ = 1 := by
    have hh := hm 0 1 (by decide)
    simpa [dist_eq_norm,norm_sub_rev,hnx] using hh.symm
  have hmy : ‖m‖+‖y-m‖ = 1 := by
    have hh := hm 0 2 (by decide)
    simpa [dist_eq_norm,norm_sub_rev,hny] using hh.symm
  have hm0 : m = 0 := by
    by_contra hh
    exact Set.disjoint_left.mp hdis (normalized_summand_mem_face hF hx hnx hh hmx)
      (normalized_summand_mem_face hG hy hny hh hmy)
  have hh := hm 1 2 (by decide)
  simpa [hm0,dist_zero_left,dist_zero_right,hnx,hny,show (1:ℝ)+1=2 by norm_num] using hh

theorem disjoint_faces_opposite_support [FiniteDimensional ℝ E]
    (hmed : HasMetricMedians E) {F G : Set E}
    (hF : IsExtreme ℝ (closedBall (0:E) 1) F)
    (hG : IsExtreme ℝ (closedBall (0:E) 1) G)
    (hFc : Convex ℝ F) (hGc : Convex ℝ G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hdis : Disjoint F G) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ = 1 ∧ (∀ x ∈ F, f x = 1) ∧ ∀ y ∈ G, f y = -1 := by
  have hsep : Disjoint (ball (0:E) 2) (F-G) := by
    rw [Set.disjoint_left]
    intro z hz hzg
    obtain ⟨x,hx,y,hy,rfl⟩ := Set.mem_sub.mp hzg
    have hn : ‖x-y‖ = 2 := by rw [← dist_eq_norm]; exact disjoint_faces_distance_two hmed hF hG hdis hx hy
    simp [hn] at hz
  obtain ⟨f,u,hlo,hhi⟩ := geometric_hahn_banach_open (convex_ball (0:E) 2) isOpen_ball
    (hFc.sub hGc) hsep
  have hclosed : ∀ z ∈ closedBall (0:E) 2, f z ≤ u := by
    have hc : closure (ball (0:E) 2) ⊆ f ⁻¹' Iic u :=
      closure_minimal (fun z hz => (hlo z hz).le) (isClosed_Iic.preimage f.continuous)
    rwa [closure_ball 0 (by norm_num : (2:ℝ) ≠ 0)] at hc
  have hu : 0 < u := by simpa using hlo 0 (by simp : (0:E) ∈ ball 0 2)
  obtain ⟨v,hv,hfv⟩ := exists_unitBall_dual_maximizer f
  have hnu : 2*‖f‖ ≤ u := by
    have hh := hclosed ((2:ℝ) • v) (by
      rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith)
    simpa [hfv] using hh
  have hxy (x : E) (hx : x ∈ F) (y : E) (hy : y ∈ G) :
      f x - f y = 2*‖f‖ := by
    have ha := hhi (x-y) (Set.sub_mem_sub hx hy)
    have hb := f.le_opNorm (x-y)
    have hn : ‖x-y‖ = 2 := by rw [← dist_eq_norm]; exact disjoint_faces_distance_two hmed hF hG hdis hx hy
    rw [map_sub] at ha hb
    rw [hn,Real.norm_eq_abs] at hb
    have hab := le_abs_self (f x-f y)
    linarith
  obtain ⟨x0,hx0⟩ := hFn
  obtain ⟨y0,hy0⟩ := hGn
  have hfp : 0 < ‖f‖ := by
    have hu' := hhi (x0-y0) (Set.sub_mem_sub hx0 hy0)
    rw [map_sub,hxy x0 hx0 y0 hy0] at hu'
    linarith
  have hfup (z : E) (hz : z ∈ closedBall (0:E) 1) : |f z| ≤ ‖f‖ :=
    (f.le_opNorm z).trans (by nlinarith [norm_nonneg f,mem_closedBall_zero_iff.mp hz])
  refine ⟨‖f‖⁻¹ • f,?_,?_,?_⟩
  · simp [norm_smul,hfp.ne']
  · intro x hx
    have hfx : f x = ‖f‖ := by
      have ha := hxy x hx y0 hy0
      have hb := (abs_le.mp (hfup x (hF.subset hx))).2
      have hc := (abs_le.mp (hfup y0 (hG.subset hy0))).1
      linarith
    simp [hfx,hfp.ne']
  · intro y hy
    have hfy : f y = -‖f‖ := by
      have ha := hxy x0 hx0 y hy
      have hb := (abs_le.mp (hfup y (hG.subset hy))).1
      have hc := (abs_le.mp (hfup x0 (hF.subset hx0))).2
      linarith
    simp [hfy,hfp.ne']

end

open Set Metric

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma bidual_functional_representation [FiniteDimensional ℝ E]
    (L : (E →L[ℝ] ℝ) →L[ℝ] ℝ) : ∃ x : E, ∀ f : E →L[ℝ] ℝ, L f = f x := by
  let L' : Module.Dual ℝ (Module.Dual ℝ E) :=
    L.toLinearMap.comp (LinearMap.toContinuousLinearMap : Module.Dual ℝ E ≃ₗ[ℝ] (E →L[ℝ] ℝ)).toLinearMap
  let x := (Module.evalEquiv ℝ E).symm L'
  refine ⟨x,?_⟩
  intro f
  have hh := Module.apply_evalEquiv_symm_apply ℝ E f.toLinearMap L'
  exact hh.symm

theorem dual_ball_eq_convexHull_opposite_faces [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {e : E}
    (he : e ∈ (closedBall (0:E) 1).extremePoints ℝ) :
    closedBall (0 : E →L[ℝ] ℝ) 1 =
      convexHull ℝ {f : E →L[ℝ] ℝ | ‖f‖ ≤ 1 ∧ (f e = 1 ∨ f e = -1)} := by
  let S := {f : E →L[ℝ] ℝ | ‖f‖ ≤ 1 ∧ (f e = 1 ∨ f e = -1)}
  have hSc : IsCompact S := by
    have hclosed : IsClosed {f : E →L[ℝ] ℝ | f e = 1 ∨ f e = -1} :=
      (isClosed_eq (by fun_prop) continuous_const).union
        (isClosed_eq (by fun_prop) continuous_const)
    have hs_eq : S = closedBall (0 : E →L[ℝ] ℝ) 1 ∩ {f | f e = 1 ∨ f e = -1} := by
      ext f
      simp only [S, Set.mem_ofPred, mem_inter_iff, mem_closedBall_zero_iff]
    rw [hs_eq]
    exact (isCompact_closedBall (0 : E →L[ℝ] ℝ) 1).inter_right hclosed
  have hsub : convexHull ℝ S ⊆ closedBall (0 : E →L[ℝ] ℝ) 1 :=
    convexHull_min (fun f hf => mem_closedBall_zero_iff.mpr hf.1) (convex_closedBall _ _)
  apply subset_antisymm _ hsub
  intro f hf
  by_contra hnot
  obtain ⟨L,u,hlo,hhi⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ S)
    (isCompact_convexHull_of_isCompact hSc).isClosed hnot
  obtain ⟨x,hx⟩ := bidual_functional_representation L
  obtain ⟨g,hgn,hgx,hge⟩ := extreme_unit_dual_face_norming hmed he x
  have hless := hlo g (subset_convexHull ℝ S ⟨hgn,hge⟩)
  rw [hx,hgx] at hless
  rw [hx] at hhi
  have hle := dual_eval_le_unit_norm f (mem_closedBall_zero_iff.mp hf) x
  linarith

theorem extreme_dual_eval_eq_one_or_neg_one [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {e : E} {f : E →L[ℝ] ℝ}
    (he : e ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    f e = 1 ∨ f e = -1 := by
  rw [dual_ball_eq_convexHull_opposite_faces hmed he] at hf
  exact (extremePoints_convexHull_subset hf).2

lemma dual_eval_bounds {f : E →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) {x : E}
    (hx : x ∈ closedBall (0:E) 1) : -1 ≤ f x ∧ f x ≤ 1 := by
  have hn := mem_closedBall_zero_iff.mp hx
  have hp := dual_eval_le_unit_norm f hf x
  have hm := dual_eval_le_unit_norm f hf (-x)
  simp only [map_neg,norm_neg] at hm
  constructor <;> linarith

lemma norm_le_of_dual_extreme_le [FiniteDimensional ℝ E] {x : E} {r : ℝ}
    (h : ∀ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, f x ≤ r) :
    ‖x‖ ≤ r := by
  let S : Set (E →L[ℝ] ℝ) := {f | f x ≤ r}
  have hS : Convex ℝ S := by
    intro f hf g hg a b ha hb hab
    change a * f x + b * g x ≤ r
    change f x ≤ r at hf
    change g x ≤ r at hg
    nlinarith [mul_nonneg ha (sub_nonneg.mpr hf),
      mul_nonneg hb (sub_nonneg.mpr hg),
      congrArg (fun t : ℝ => t*r) hab]
  have hcl : IsClosed S := isClosed_le (by fun_prop) continuous_const
  have hs : closedBall (0 : E →L[ℝ] ℝ) 1 ⊆ S := by
    rw [← closure_convexHull_extremePoints (isCompact_closedBall _ _) (convex_closedBall _ _)]
    exact closure_minimal (convexHull_min h hS) hcl
  obtain ⟨f,hf,he⟩ := exists_dual_vector'' ℝ x
  have hh := hs (mem_closedBall_zero_iff.mpr hf)
  change f x ≤ r at hh
  rwa [he] at hh

lemma eq_of_dual_extreme_eq [FiniteDimensional ℝ E] {x y : E}
    (h : ∀ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, f x = f y) : x = y := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  apply norm_le_of_dual_extreme_le
  intro f hf
  simp [h f hf]

lemma extreme_of_dual_levels [FiniteDimensional ℝ E] {x : E}
    (hx : x ∈ closedBall (0:E) 1)
    (h : ∀ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, f x = 1 ∨ f x = -1) :
    x ∈ (closedBall (0:E) 1).extremePoints ℝ := by
  refine ⟨hx, ?_⟩
  intro y hy z hz hseg
  obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
  apply eq_of_dual_extreme_eq
  intro f hf
  have hfy := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hy
  have hfz := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hz
  have hev := congrArg f he
  simp only [map_add,map_smul,smul_eq_mul] at hev
  rcases h f hf with hh | hh
  · rw [hh] at hev ⊢
    have hprod : a * (1 - f y) = 0 := by
      nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hfy.2),
        mul_nonneg hb.le (sub_nonneg.mpr hfz.2)]
    have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
    linarith
  · rw [hh] at hev ⊢
    have hprod : a * (f y + 1) = 0 := by
      nlinarith [mul_nonneg ha.le (show 0 ≤ f y+1 by linarith),
        mul_nonneg hb.le (show 0 ≤ f z+1 by linarith)]
    have := (mul_eq_zero.mp hprod).resolve_left (ne_of_gt ha)
    linarith

lemma isFace_support {f : E →L[ℝ] ℝ} (hf : ‖f‖ ≤ 1) :
    IsFace (closedBall (0:E) 1) {x ∈ closedBall (0:E) 1 | f x = 1} := by
  constructor
  · intro x hx y hy a b ha hb hab
    refine ⟨(convex_closedBall _ _) hx.1 hy.1 ha hb hab, ?_⟩
    simp [hx.2,hy.2,hab]
  · refine ⟨fun x hx => hx.1, ?_⟩
    intro x hx y hy z hz hseg
    obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
    refine ⟨hx, ?_⟩
    have hfx := (dual_eval_bounds hf hx).2
    have hfy := (dual_eval_bounds hf hy).2
    have hev := congrArg f he
    simp only [map_add,map_smul,smul_eq_mul,hz.2] at hev
    nlinarith

lemma isFace_exchangeFace [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {x y : E}
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ) :
    IsFace (closedBall (0:E) 1) (exchangeFace x y) := by
  constructor
  · intro u hu v hv a b ha hb hab
    refine ⟨(convex_closedBall _ _) hu.1 hv.1 ha hb hab, ?_⟩
    have he : x+(a • u+b • v)-y = a • (x+u-y)+b • (x+v-y) := by
      calc
        _ = (a+b) • x+(a • u+b • v)-(a+b) • y := by rw [hab]; simp
        _ = _ := by module
    rw [he]
    exact (convex_closedBall _ _) hu.2 hv.2 ha hb hab
  · refine ⟨fun u hu => hu.1, ?_⟩
    intro u hu v hv z hz hseg
    obtain ⟨a,b,ha,hb,hab,he⟩ := hseg
    refine ⟨hu, mem_closedBall_zero_iff.mpr ?_⟩
    apply norm_le_of_dual_extreme_le
    intro f hf
    have hfu := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hu
    have hfv := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hv
    have hfz := (dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hz.2).2
    have hev := congrArg f he
    simp only [map_add,map_smul,smul_eq_mul] at hev
    simp only [map_add,map_sub] at hfz ⊢
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with hfx | hfx <;>
      rcases extreme_dual_eval_eq_one_or_neg_one hmed hy hf with hfy | hfy <;>
      rw [hfx,hfy] at hfz ⊢ <;> nlinarith

lemma exchange_vertex [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {x y u : E}
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hu : u ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hex : u ∈ exchangeFace x y) :
    x+u-y ∈ (closedBall (0:E) 1).extremePoints ℝ := by
  apply extreme_of_dual_levels hex.2
  intro f hf
  have hb := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hex.2
  simp only [map_sub,map_add] at hb ⊢
  rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with hfx | hfx <;>
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hy hf with hfy | hfy <;>
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hu hf with hfu | hfu <;>
    simp_all <;> linarith

theorem face_vertex_exchange [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) {x y : E} {F : Set E}
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hF : IsFace (closedBall (0:E) 1) F) (hFn : F.Nonempty)
    (hyF : y ∈ faceHull (closedBall (0:E) 1) ({x} ∪ F)) :
    ∃ u ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ v ∈ (closedBall (0:E) 1).extremePoints ℝ, x+u = y+v := by
  let C := exchangeFace x y
  have hC : IsFace (closedBall (0:E) 1) C := isFace_exchangeFace hmed hx hy
  have hyC : y ∈ C := ⟨hy.1, by simpa using hx.1⟩
  have hnxC : -x ∈ C := ⟨by simpa using hx.1, by simpa using hy.1⟩
  have hinter : (F ∩ C).Nonempty := by
    by_contra hh
    have hdis : Disjoint F C := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hh)
    obtain ⟨f,hfn,hfF,hfC⟩ := disjoint_faces_opposite_support hmed hF.2 hC.2
      hF.1 hC.1 hFn ⟨y,hyC⟩ hdis
    have hfx : f x = 1 := by have ht := hfC _ hnxC; simpa using ht
    have hfy := hfC y hyC
    have hsub : {x} ∪ F ⊆ {z ∈ closedBall (0:E) 1 | f z = 1} := by
      rintro z (rfl | hz)
      · exact ⟨hx.1,hfx⟩
      · exact ⟨hF.subset hz,hfF z hz⟩
    have hh' := (faceHull_min (isFace_support hfn.le) hsub hyF).2
    linarith
  obtain ⟨V,hV,hball⟩ := unitBall_eq_finite_convexHull_of_medians hmed
  have hFC := hF.inter hC
  have hcompact : IsCompact (F ∩ C) := by
    apply IsFace.isCompact_of_finite_hull hV
    rwa [← hball]
  obtain ⟨u,hu⟩ := hcompact.extremePoints_nonempty hinter
  have hub := hFC.2.extremePoints_subset_extremePoints hu
  exact ⟨u,⟨hu.1.1,hub⟩,x+u-y,exchange_vertex hmed hx hy hub hu.1.2,by abel⟩

lemma IsFace.singleton {K : Set E} {x : E} (hx : x ∈ K.extremePoints ℝ) :
    IsFace K {x} := ⟨convex_singleton _, isExtreme_singleton.mpr hx⟩

lemma IsFace.extremePoints_eq {K F : Set E} (hF : IsFace K F) :
    F.extremePoints ℝ = K.extremePoints ℝ ∩ F := by
  apply subset_antisymm
  · exact fun x hx => ⟨hF.2.extremePoints_subset_extremePoints hx,hx.1⟩
  · intro x hx
    exact ⟨hx.2,fun y hy z hz hs => hx.1.2 (hF.subset hy) (hF.subset hz) hs⟩

variable [inst472 : FiniteDimensional ℝ E] [inst473 : Nontrivial E]

lemma unitBall_eq_convexHull_extreme (hmed : HasMetricMedians E) :
    closedBall (0:E) 1 = convexHull ℝ ((closedBall (0:E) 1).extremePoints ℝ) := by
  have h := closure_convexHull_extremePoints (isCompact_closedBall (0:E) 1)
    (convex_closedBall (0:E) 1)
  rw [((finite_extreme_unit_of_medians hmed).isClosed_convexHull ℝ).closure_eq] at h
  exact h.symm

lemma IsFace.isCompact_unit (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) : IsCompact F := by
  apply IsFace.isCompact_of_finite_hull (finite_extreme_unit_of_medians hmed)
  rwa [← unitBall_eq_convexHull_extreme hmed]

lemma IsFace.eq_convexHull_vertices (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) :
    F = convexHull ℝ ((closedBall (0:E) 1).extremePoints ℝ ∩ F) := by
  apply IsFace.eq_convexHull_inter
  rwa [← unitBall_eq_convexHull_extreme hmed]

lemma IsFace.exists_vertex (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty) :
    ∃ x ∈ (closedBall (0:E) 1).extremePoints ℝ, x ∈ F := by
  obtain ⟨x,hx⟩ := (hF.isCompact_unit hmed).extremePoints_nonempty hn
  exact ⟨x,hF.2.extremePoints_subset_extremePoints hx,hx.1⟩

lemma IsFace.subset_of_vertices (hmed : HasMetricMedians E) {F G : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hG : Convex ℝ G)
    (h : (closedBall (0:E) 1).extremePoints ℝ ∩ F ⊆ G) : F ⊆ G := by
  rw [hF.eq_convexHull_vertices hmed]
  exact convexHull_min h hG

lemma IsFace.exists_vertex_outside (hmed : HasMetricMedians E) {F K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : Convex ℝ F) (hn : ¬ K ⊆ F) :
    ∃ x ∈ (closedBall (0:E) 1).extremePoints ℝ, x ∈ K ∧ x ∉ F := by
  classical
  by_contra! h
  apply hn
  exact hK.subset_of_vertices hmed hF (fun x hx => h x hx.1 hx.2)

omit inst472 inst473 in
lemma isFace_dual_common [FiniteDimensional ℝ E] [Nontrivial E] {A : Set E} (hA : A ⊆ closedBall (0:E) 1) :
    IsFace (closedBall (0 : E →L[ℝ] ℝ) 1)
      {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ x ∈ A, f x = 1} := by
  constructor
  · intro f hf g hg a b ha hb hab
    refine ⟨(convex_closedBall _ _) hf.1 hg.1 ha hb hab, ?_⟩
    intro x hx
    simp [hf.2 x hx,hg.2 x hx,hab]
  · refine ⟨fun f hf => hf.1, ?_⟩
    intro f hf g hg k hk hs
    obtain ⟨a,b,ha,hb,hab,he⟩ := hs
    refine ⟨hf, fun x hx => ?_⟩
    have hfx := (dual_eval_bounds (mem_closedBall_zero_iff.mp hf) (hA hx)).2
    have hgx := (dual_eval_bounds (mem_closedBall_zero_iff.mp hg) (hA hx)).2
    have hev := congrArg (fun q : E →L[ℝ] ℝ => q x) he
    simp only [add_apply, smul_apply,
      smul_eq_mul, hk.2 x hx] at hev
    nlinarith

omit inst473 in
lemma isCompact_dual_common [Nontrivial E] (A : Set E) :
    IsCompact {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ x ∈ A, f x = 1} := by
  apply (isCompact_closedBall _ _).inter_right
  change IsClosed {f : E →L[ℝ] ℝ | ∀ x ∈ A, f x = 1}
  have he : {f : E →L[ℝ] ℝ | ∀ x ∈ A, f x = 1} =
      ⋂ x ∈ A, {f : E →L[ℝ] ℝ | f x = 1} := by ext f; simp
  rw [he]
  exact isClosed_biInter (fun x _ => isClosed_eq (by fun_prop) continuous_const)

lemma face_vertex_dual_separation (hmed : HasMetricMedians E) {F : Set E} {x : E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty)
    (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ) (hxn : x ∉ F) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ y ∈ F, f y = 1) ∧ f x = -1 := by
  have hd : Disjoint F {x} := by simpa using hxn
  obtain ⟨g,hg,hgF,hgx⟩ := disjoint_faces_opposite_support hmed hF.2
    (IsFace.singleton hx).2 hF.1 (convex_singleton x) hn (singleton_nonempty x) hd
  let A := F ∪ {-x}
  have hA : A ⊆ closedBall (0:E) 1 := by
    rintro y (hy | rfl)
    · exact hF.subset hy
    · simpa using hx.1
  have hnD : {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ y ∈ A, f y = 1}.Nonempty := by
    refine ⟨g,mem_closedBall_zero_iff.mpr hg.le,?_⟩
    rintro y (hy | rfl)
    · exact hgF y hy
    · simp [hgx x (mem_singleton x)]
  obtain ⟨f,hf⟩ := (isCompact_dual_common A).extremePoints_nonempty hnD
  refine ⟨f,(isFace_dual_common hA).2.extremePoints_subset_extremePoints hf,
    fun y hy => hf.1.2 y (Or.inl hy), ?_⟩
  have hh := hf.1.2 (-x) (Or.inr (mem_singleton _))
  simp only [map_neg] at hh
  linarith

namespace IsParallelPair
variable {K F G : Set E}
omit inst472 inst473 in
lemma symm [FiniteDimensional ℝ E] [Nontrivial E] (h : IsParallelPair K F G) : IsParallelPair K G F :=
  ⟨h.2.1,h.1,h.2.2.1.symm,by simpa [union_comm] using h.2.2.2⟩
omit inst472 inst473 in
lemma vertex_mem [FiniteDimensional ℝ E] [Nontrivial E] (h : IsParallelPair K F G) {x : E} (hx : x ∈ K.extremePoints ℝ) :
    x ∈ F ∨ x ∈ G := by
  rw [h.2.2.2] at hx
  exact (show x ∈ F ∪ G from extremePoints_convexHull_subset hx)
lemma not_mem_iff (h : IsParallelPair K F G) {x : E} (hx : x ∈ K.extremePoints ℝ) :
    x ∉ F ↔ x ∈ G := by
  constructor
  · intro hn
    exact (h.vertex_mem hx).resolve_left hn
  · exact fun hg hf => Set.disjoint_left.mp h.2.2.1 hf hg
end IsParallelPair

lemma parallelPair_of_dual_vertex (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) {f : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    IsParallelPair K {x ∈ K | f x = 1} {x ∈ K | f x = -1} := by
  have heF : K ∩ {x ∈ closedBall (0:E) 1 | f x = 1} = {x ∈ K | f x = 1} := by
    ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hK.subset h.1,h.2⟩⟩
  have hF : IsFace (closedBall (0:E) 1) {x ∈ K | f x = 1} := by
    rw [← heF]
    exact hK.inter (isFace_support (mem_closedBall_zero_iff.mp hf.1))
  have hG : IsFace (closedBall (0:E) 1) {x ∈ K | f x = -1} := by
    have hh := hK.inter (isFace_support (f := -f) (by simpa using mem_closedBall_zero_iff.mp hf.1))
    have he : K ∩ {x ∈ closedBall (0:E) 1 | (-f) x = 1} = {x ∈ K | f x = -1} := by
      ext x
      constructor
      · rintro ⟨hx,hxb,hfx⟩
        refine ⟨hx,?_⟩
        change -f x = 1 at hfx
        linarith
      · rintro ⟨hx,hfx⟩
        exact ⟨hx,hK.subset hx,by simp [hfx]⟩
    rwa [he] at hh
  refine ⟨hF.mono hK.subset (fun _ h => h.1),hG.mono hK.subset (fun _ h => h.1),?_,?_⟩
  · exact disjoint_left.mpr (fun x hx hy => by linarith [hx.2,hy.2])
  · apply subset_antisymm
    · apply hK.subset_of_vertices hmed (convex_convexHull _ _)
      intro x hx
      apply subset_convexHull
      rcases extreme_dual_eval_eq_one_or_neg_one hmed hx.1 hf with h | h
      · exact Or.inl ⟨hx.2,h⟩
      · exact Or.inr ⟨hx.2,h⟩
    · exact convexHull_min (union_subset (fun _ h => h.1) (fun _ h => h.1)) hK.1

theorem maximal_avoiding_vertex_parallel (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : IsFace K F) (hn : F.Nonempty)
    (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F)
    (hmax : ∀ G, IsFace K G → F ⊆ G → x ∉ G → G ⊆ F) :
    IsParallelFace K F := by
  obtain ⟨f,hf,hfF,hfx⟩ := face_vertex_dual_separation hmed (hK.trans hF) hn
    (hK.2.extremePoints_subset_extremePoints hx) hxn
  have hp := parallelPair_of_dual_vertex hmed hK hf
  have he : {z ∈ K | f z = 1} = F := subset_antisymm
    (hmax _ hp.1 (fun z hz => ⟨hF.subset hz,hfF z hz⟩) (by intro hh; linarith [hh.2]))
    (fun z hz => ⟨hF.subset hz,hfF z hz⟩)
  exact ⟨_,he ▸ hp⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst476 : FiniteDimensional ℝ E] [inst477 : Nontrivial E]

omit inst476 inst477 in
lemma face_mem_of_parallelogram [FiniteDimensional ℝ E] [Nontrivial E] {K F : Set E} (hF : IsFace K F)
    {x u y v : E} (hx : x ∈ F) (hu : u ∈ F) (hy : y ∈ K) (hv : v ∈ K)
    (he : x+u = y+v) : y ∈ F ∧ v ∈ F := by
  have hm : (1/2:ℝ) • x+(1/2:ℝ) • u ∈ F :=
    hF.1 hx hu (by norm_num) (by norm_num) (by norm_num)
  have hs : (1/2:ℝ) • x+(1/2:ℝ) • u ∈ openSegment ℝ y v := by
    refine ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,?_⟩
    simpa only [smul_add] using congrArg (fun z : E => (1/2:ℝ) • z) he.symm
  exact ⟨hF.2.left_mem_of_mem_openSegment hy hv hm hs,
    hF.2.right_mem_of_mem_openSegment hy hv hm hs⟩

lemma proper_face_support (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    (hp : K ≠ closedBall (0:E) 1) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ, ∀ x ∈ K, f x = 1 := by
  obtain ⟨x,hx,-,hxn⟩ := (IsFace.refl (convex_closedBall (0:E) 1)).exists_vertex_outside
    hmed hK.1 (by intro hh; exact hp (subset_antisymm hK.subset hh))
  obtain ⟨f,hf,hfK,-⟩ := face_vertex_dual_separation hmed hK hn hx hxn
  exact ⟨f,hf,hfK⟩

lemma vertex_not_mem_span_face (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F) :
    x ∉ Submodule.span ℝ F := by
  by_cases hn : F.Nonempty
  · obtain ⟨f,hf,hfF,hfx⟩ := face_vertex_dual_separation hmed (hK.trans hF) hn
      (hK.2.extremePoints_subset_extremePoints hx) hxn
    obtain ⟨g,hg,hgK⟩ := proper_face_support hmed hK ⟨x,hx.1⟩ hp
    have hs : Submodule.span ℝ F ≤ (f-g).toLinearMap.ker := by
      apply Submodule.span_le.mpr
      intro y hy
      change f y-g y = 0
      rw [hfF y hy,hgK y (hF.subset hy)]
      ring
    intro hh
    have hz := hs hh
    change f x-g x = 0 at hz
    rw [hfx,hgK x hx.1] at hz
    norm_num at hz
  · rw [not_nonempty_iff_eq_empty.mp hn,Submodule.span_empty]
    intro hx0
    have he : x = 0 := hx0
    have hh := norm_eq_one_of_mem_proper_face hK.2 hp hx.1
    simp [he] at hh

lemma faceRank_lt (hmed : HasMetricMedians E) {F K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hne : F ≠ K) : faceRank F < faceRank K := by
  obtain ⟨x,hx,hxK,hxn⟩ := hK.exists_vertex_outside hmed hF.1
    (by intro hh; exact hne (subset_antisymm hF.subset hh))
  apply Submodule.finrank_lt_finrank_of_lt
  refine lt_of_le_of_ne (Submodule.span_mono hF.subset) ?_
  intro he
  apply vertex_not_mem_span_face hmed hK hp hF
    (by rw [hK.extremePoints_eq]; exact ⟨hx,hxK⟩) hxn
  rw [he]
  exact Submodule.subset_span hxK

lemma parallel_face_vertex_exchange (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hpair : IsParallelPair K F G)
    (hFn : F.Nonempty) {x y : E} (hx : x ∈ K.extremePoints ℝ) (_ : x ∈ G)
    (hy : y ∈ K.extremePoints ℝ) (hyG : y ∈ G)
    (hyH : y ∈ faceHull (closedBall (0:E) 1) ({x} ∪ F)) :
    ∃ u ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ v ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ, x+u = y+v := by
  obtain ⟨u,hu,v,hv,he⟩ := face_vertex_exchange hmed
    (hK.2.extremePoints_subset_extremePoints hx) (hK.2.extremePoints_subset_extremePoints hy)
    (hK.trans hpair.1) hFn hyH
  have hvK := (face_mem_of_parallelogram hK hx.1 (hpair.1.subset hu.1) (hK.subset hy.1) hv.1 he).2
  have hvKex : v ∈ K.extremePoints ℝ := by rw [hK.extremePoints_eq]; exact ⟨hv,hvK⟩
  have hvF : v ∈ F := by
    rcases hpair.vertex_mem hvKex with hh | hh
    · exact hh
    · have huG := (face_mem_of_parallelogram hpair.2.1 hyG hh hx.1
        (hpair.1.subset hu.1) he.symm).2
      exact False.elim (disjoint_left.mp hpair.2.2.1 hu.1 huG)
  exact ⟨u,hu,v,⟨hvF,hv⟩,he⟩

theorem parallel_faceHull_rank (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G) (hFn : F.Nonempty) {x : E}
    (hx : x ∈ K.extremePoints ℝ) (hxG : x ∈ G) :
    faceRank (faceHull (closedBall (0:E) 1) ({x} ∪ F)) = faceRank F + 1 := by
  let H := faceHull (closedBall (0:E) 1) ({x} ∪ F)
  have hsub : {x} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hx.1) hpair.1.subset
  have hH : IsFace (closedBall (0:E) 1) H :=
    isFace_faceHull (convex_closedBall _ _) (hsub.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hsub
  have hs : Submodule.span ℝ H = Submodule.span ℝ ({x} ∪ F) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      apply hH.subset_of_vertices hmed (Submodule.convex _)
      intro y hy
      have hyK : y ∈ K.extremePoints ℝ := by rw [hK.extremePoints_eq]; exact ⟨hy.1,hHK hy.2⟩
      rcases hpair.vertex_mem hyK with hyF | hyG
      · exact Submodule.subset_span (Or.inr hyF)
      · obtain ⟨u,hu,v,hv,he⟩ := parallel_face_vertex_exchange hmed hK hpair hFn hx hxG hyK hyG hy.2
        have hey : y = x+u-v := by rw [he]; abel
        rw [hey]
        exact (Submodule.span ℝ ({x} ∪ F)).sub_mem
          ((Submodule.span ℝ ({x} ∪ F)).add_mem
            (Submodule.subset_span (Or.inl (mem_singleton x)))
            (Submodule.subset_span (Or.inr hu.1)))
          (Submodule.subset_span (Or.inr hv.1))
    · exact Submodule.span_mono subset_faceHull
  unfold faceRank
  rw [hs,Submodule.span_union,sup_comm]
  exact Submodule.finrank_sup_span_singleton
    (vertex_not_mem_span_face hmed hK hp hpair.1 hx ((hpair.not_mem_iff hx).mpr hxG))

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma parallelogram_not_parallel {K F : Set E}
    {x y u v : E} (hxF : x ∈ F) (hxK : x ∈ K)
    (hyK : y ∈ K) (hu : u ∈ K.extremePoints ℝ) (hv : v ∈ K.extremePoints ℝ)
    (huF : u ∉ F) (hvF : v ∉ F) (he : x+y = u+v) :
    ¬ IsParallelFace K F := by
  rintro ⟨G,hpair⟩
  have huG := (hpair.not_mem_iff hu).mp huF
  have hvG := (hpair.not_mem_iff hv).mp hvF
  have hxG := (face_mem_of_parallelogram hpair.2.1 huG hvG hxK hyK he.symm).1
  exact disjoint_left.mp hpair.2.2.1 hxF hxG

theorem nonparallel_vertex_parallelogram (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : IsFace K F)
    (_ : F.Nonempty) (hp : F ≠ K) (hnp : ¬ IsParallelFace K F) :
    ∃ x ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ y ∈ (K \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
        ∃ u ∈ (K \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
          ∃ v ∈ (K \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ, x+y = u+v := by
  classical
  obtain ⟨z,hz,hzK,hzF⟩ := hK.exists_vertex_outside hmed hF.1
    (by intro hh; exact hp (subset_antisymm hF.subset hh))
  let D : Set (Set E) := {S | IsFace (closedBall (0:E) 1) S ∧ S ⊆ K ∧
    Disjoint F S ∧ z ∈ S}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset (fun _ h => h.1)
  have hDn : D.Nonempty := by
    refine ⟨{z},IsFace.singleton hz,singleton_subset_iff.mpr hzK,?_,mem_singleton z⟩
    simpa using hzF
  obtain ⟨S,hSmax⟩ := hDf.exists_maximal hDn
  have hSD : S ∈ D := hSmax.1
  obtain ⟨hS,hSK,hFS,hzS⟩ := hSD
  have hSc : IsFace K S := hS.mono hK.subset hSK
  have hnot : ¬ K ⊆ convexHull ℝ (F ∪ S) := by
    intro hh
    apply hnp
    refine ⟨S,hF,hSc,hFS,subset_antisymm hh ?_⟩
    exact convexHull_min (union_subset hF.subset hSK) hK.1
  obtain ⟨u,hu,huK,huN⟩ := hK.exists_vertex_outside hmed (convex_convexHull ℝ (F ∪ S)) hnot
  have huF : u ∉ F := fun hh => huN (subset_convexHull ℝ _ (Or.inl hh))
  have huS : u ∉ S := fun hh => huN (subset_convexHull ℝ _ (Or.inr hh))
  let H := faceHull (closedBall (0:E) 1) ({u} ∪ S)
  have hbase : {u} ∪ S ⊆ K := union_subset (singleton_subset_iff.mpr huK) hSK
  have hH : IsFace (closedBall (0:E) 1) H :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hbase
  have hSH : S ⊆ H := fun x hx => subset_faceHull (Or.inr hx)
  have huH : u ∈ H := subset_faceHull (Or.inl (mem_singleton u))
  have hI : (F ∩ H).Nonempty := by
    by_contra hni
    have hdis : Disjoint F H := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hni)
    have hHD : H ∈ D := ⟨hH,hHK,hdis,hSH hzS⟩
    exact huS (hSmax.2 hHD hSH huH)
  have hIF : IsFace (closedBall (0:E) 1) (F ∩ H) := (hK.trans hF).inter hH
  obtain ⟨x,hx,hxFH⟩ := hIF.exists_vertex hmed hI
  obtain ⟨v,hv,y,hy,he⟩ := face_vertex_exchange hmed hu hx hS ⟨z,hzS⟩ hxFH.2
  have hyK := (face_mem_of_parallelogram hK huK (hSK hv.1) (hK.subset (hF.subset hxFH.1)) hy.1 he).2
  have hyF : y ∉ F := by
    intro hyF
    have huF' := (face_mem_of_parallelogram hF hxFH.1 hyF huK (hSK hv.1) he.symm).1
    exact huF huF'
  exact ⟨x,⟨hxFH.1,hx⟩,y,⟨⟨hyK,hyF⟩,hy⟩,u,⟨⟨huK,huF⟩,hu⟩,
    v,⟨⟨hSK hv.1,fun hh => disjoint_left.mp hFS hh hv.1⟩,hv.2⟩,he.symm⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [inst485 : Nontrivial E]

omit inst485 in
lemma faceRank_mono [Nontrivial E] {F G : Set E} (h : F ⊆ G) : faceRank F ≤ faceRank G :=
  Submodule.finrank_mono (Submodule.span_mono h)

omit inst485 in
lemma faceRank_le_dim [Nontrivial E] (F : Set E) : faceRank F ≤ Module.finrank ℝ E :=
  Submodule.finrank_le _

lemma rank_succ_maximal (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hne : F ≠ K) (hr : faceRank K = faceRank F + 1) :
    IsMaximalProperFace K F := by
  refine ⟨hF,hne,?_⟩
  intro G hG hFG hGp
  by_contra hGF
  have h1 := faceRank_lt hmed hK hp hG hGp
  have hGproper : G ≠ closedBall (0:E) 1 := by
    intro hh
    exact hp (subset_antisymm hK.subset (hh ▸ hG.subset))
  have h2 := faceRank_lt hmed (hK.trans hG) hGproper
    (hF.mono hG.subset hFG) (Ne.symm hGF)
  omega

theorem maximal_avoiding_vertex_rank (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hFn : F.Nonempty)
    (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F)
    (hmax : ∀ G, IsFace K G → F ⊆ G → x ∉ G → G ⊆ F) :
    faceRank K = faceRank F + 1 ∧ IsMaximalProperFace K F := by
  obtain ⟨G,hpair⟩ := maximal_avoiding_vertex_parallel hmed hK hF hFn hx hxn hmax
  have hxG := (hpair.not_mem_iff hx).mp hxn
  have hspan : Submodule.span ℝ K = Submodule.span ℝ ({x} ∪ F) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      apply hK.subset_of_vertices hmed (Submodule.convex _)
      intro y hy
      have hyK : y ∈ K.extremePoints ℝ := by rw [hK.extremePoints_eq]; exact hy
      rcases hpair.vertex_mem hyK with hyF | hyG
      · exact Submodule.subset_span (Or.inr hyF)
      · let H := faceHull (closedBall (0:E) 1) ({y} ∪ F)
        have hbase : {y} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hy.2) hF.subset
        have hH : IsFace (closedBall (0:E) 1) H :=
          isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.subset)
        have hHK : H ⊆ K := faceHull_min hK hbase
        have hFH : F ⊆ H := fun _ hz => subset_faceHull (Or.inr hz)
        have hxH : x ∈ H := by
          by_contra hn
          exact disjoint_left.mp hpair.2.2.1
            (hmax H (hH.mono hK.subset hHK) hFH hn
              (subset_faceHull (Or.inl (mem_singleton y)))) hyG
        obtain ⟨u,hu,v,hv,he⟩ := parallel_face_vertex_exchange hmed hK hpair hFn hyK hyG hx hxG hxH
        have hey : y = x+v-u := by rw [← he]; abel
        rw [hey]
        exact (Submodule.span ℝ ({x} ∪ F)).sub_mem
          ((Submodule.span ℝ ({x} ∪ F)).add_mem
            (Submodule.subset_span (Or.inl (mem_singleton x)))
            (Submodule.subset_span (Or.inr hv.1)))
          (Submodule.subset_span (Or.inr hu.1))
    · exact Submodule.span_mono (union_subset (singleton_subset_iff.mpr hx.1) hF.subset)
  have hr : faceRank K = faceRank F + 1 := by
    unfold faceRank
    rw [hspan,Submodule.span_union,sup_comm]
    exact Submodule.finrank_sup_span_singleton (vertex_not_mem_span_face hmed hK hp hF hx hxn)
  exact ⟨hr,rank_succ_maximal hmed hK hp hF (by intro hh; exact hxn (hh.symm ▸ hx.1)) hr⟩

lemma extend_face_avoiding_vertex (hmed : HasMetricMedians E) {K F : Set E} {x : E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hFn : F.Nonempty) (hx : x ∈ K.extremePoints ℝ) (hxn : x ∉ F) :
    ∃ G, IsMaximalProperFace K G ∧ F ⊆ G ∧ x ∉ G := by
  classical
  let D : Set (Set E) := {G | IsFace K G ∧ F ⊆ G ∧ x ∉ G}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset
    (fun G hG => hK.trans hG.1)
  obtain ⟨G,hGmax⟩ := hDf.exists_maximal ⟨F,hF,Subset.rfl,hxn⟩
  have hG : G ∈ D := hGmax.1
  have hm := maximal_avoiding_vertex_rank hmed hK hp hG.1
    (hFn.mono hG.2.1) hx hG.2.2
    (fun H hH hGH hxnH => hGmax.2 ⟨hH,hG.2.1.trans hGH,hxnH⟩ hGH)
  exact ⟨G,hm.2,hG.2.1,hG.2.2⟩

lemma maximal_proper_parallel (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hF : IsMaximalProperFace K F)
    (hn : F.Nonempty) : IsParallelFace K F := by
  obtain ⟨x,hx,hxK,hxn⟩ := hK.exists_vertex_outside hmed hF.1.1
    (by intro hh; exact hF.2.1 (subset_antisymm hF.1.subset hh))
  apply maximal_avoiding_vertex_parallel hmed hK hF.1 hn
    (by rw [hK.extremePoints_eq]; exact ⟨hx,hxK⟩) hxn
  intro G hG hFG hxG
  exact (hF.2.2 G hG hFG (by intro hh; exact hxG (hh.symm ▸ hxK))).le

lemma maximal_proper_rank (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsMaximalProperFace K F) (hn : F.Nonempty) :
    faceRank K = faceRank F + 1 := by
  obtain ⟨x,hx,hxK,hxn⟩ := hK.exists_vertex_outside hmed hF.1.1
    (by intro hh; exact hF.2.1 (subset_antisymm hF.1.subset hh))
  apply (maximal_avoiding_vertex_rank hmed hK hp hF.1 hn
    (by rw [hK.extremePoints_eq]; exact ⟨hx,hxK⟩) hxn ?_).1
  intro G hG hFG hxG
  exact (hF.2.2 G hG hFG (by intro hh; exact hxG (hh.symm ▸ hxK))).le

lemma span_support_dual_vertex (hmed : HasMetricMedians E) {f : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    Submodule.span ℝ {x ∈ closedBall (0:E) 1 | f x = 1} = ⊤ := by
  let S := Submodule.span ℝ {x ∈ closedBall (0:E) 1 | f x = 1}
  have hBS : closedBall (0:E) 1 ⊆ S := by
    rw [unitBall_eq_convexHull_extreme hmed]
    apply convexHull_min _ (Submodule.convex _)
    intro x hx
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with h | h
    · exact Submodule.subset_span ⟨hx.1,h⟩
    · have hn : -x ∈ S := Submodule.subset_span ⟨by simpa using hx.1,by simp [h]⟩
      simpa using S.neg_mem hn
  apply top_unique
  intro x _
  by_cases hx : x = 0
  · simp [hx]
  have hn := norm_pos_iff.mpr hx
  have hxu : ‖x‖⁻¹ • x ∈ S := hBS (by simp [norm_smul,hn.ne'])
  change x ∈ S
  simpa [smul_smul,hn.ne'] using S.smul_mem ‖x‖ hxu

lemma full_rank_maximal_proper (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hp : F ≠ closedBall (0:E) 1)
    (hr : faceRank F = Module.finrank ℝ E) :
    IsMaximalProperFace (closedBall (0:E) 1) F := by
  refine ⟨hF,hp,?_⟩
  intro G hG hFG hGp
  by_contra hne
  have hh := faceRank_lt hmed hG hGp (hF.mono hG.subset hFG) (Ne.symm hne)
  have := faceRank_le_dim G
  omega

lemma maximal_unit_face_rank (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsMaximalProperFace (closedBall (0:E) 1) F) (hn : F.Nonempty) :
    faceRank F = Module.finrank ℝ E := by
  obtain ⟨f,hf,hfF⟩ := proper_face_support hmed hF.1 hn hF.2.1
  have hs : IsFace (closedBall (0:E) 1) {x ∈ closedBall (0:E) 1 | f x = 1} :=
    isFace_support (mem_closedBall_zero_iff.mp hf.1)
  have hp : {x ∈ closedBall (0:E) 1 | f x = 1} ≠ closedBall (0:E) 1 := by
    intro hh
    have h0 : (0:E) ∈ {x ∈ closedBall (0:E) 1 | f x = 1} := hh.symm ▸ (by simp)
    simpa using h0.2
  have he := hF.2.2 _ hs (fun x hx => ⟨hF.1.subset hx,hfF x hx⟩) hp
  unfold faceRank
  rw [← he,span_support_dual_vertex hmed hf,finrank_top]

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst488 : FiniteDimensional ℝ E] [inst489 : Nontrivial E]

omit inst488 inst489 in
lemma IsFace.extreme_mem [FiniteDimensional ℝ E] [Nontrivial E] {K F : Set E} (hF : IsFace K F) {x : E}
    (hx : x ∈ K.extremePoints ℝ) (hxF : x ∈ F) : x ∈ F.extremePoints ℝ := by
  rw [hF.extremePoints_eq]; exact ⟨hx,hxF⟩

lemma IsParallelPair.restrict (hmed : HasMetricMedians E) {K F G L : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (hL : IsFace K L) : IsParallelPair L (L ∩ F) (L ∩ G) := by
  have hLF := hL.inter h.1
  have hLG := hL.inter h.2.1
  refine ⟨hLF.mono hL.subset inter_subset_left,hLG.mono hL.subset inter_subset_left,
    h.2.2.1.mono inter_subset_right inter_subset_right,?_⟩
  apply subset_antisymm
  · apply (hK.trans hL).subset_of_vertices hmed (convex_convexHull _ _)
    intro x hx
    apply subset_convexHull
    rcases h.vertex_mem (hK.extreme_mem hx.1 (hL.subset hx.2)) with hh | hh
    · exact Or.inl ⟨hx.2,hh⟩
    · exact Or.inr ⟨hx.2,hh⟩
  · exact convexHull_min (union_subset inter_subset_left inter_subset_left) hL.1

lemma IsParallelPair.complement_anti (hmed : HasMetricMedians E) {K F G A B : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (h' : IsParallelPair K A B) (hFA : F ⊆ A) : B ⊆ G := by
  apply (hK.trans h'.2.1).subset_of_vertices hmed h.2.1.1
  intro x hx
  apply (h.not_mem_iff (hK.extreme_mem hx.1 (h'.2.1.subset hx.2))).mp
  exact fun hf => disjoint_left.mp h'.2.2.1 (hFA hf) hx.2

lemma IsParallelPair.complement_unique (hmed : HasMetricMedians E) {K F G A : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (h' : IsParallelPair K F A) : G = A :=
  subset_antisymm (h'.complement_anti hmed hK h Subset.rfl)
    (h.complement_anti hmed hK h' Subset.rfl)

lemma IsParallelPair.subset_of_disjoint (hmed : HasMetricMedians E) {K F G A : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (hA : IsFace K A) (hAF : Disjoint A F) : A ⊆ G := by
  apply (hK.trans hA).subset_of_vertices hmed h.2.1.1
  intro x hx
  exact (h.not_mem_iff (hK.extreme_mem hx.1 (hA.subset hx.2))).mp
    (fun hh => disjoint_left.mp hAF hx.2 hh)

omit inst488 inst489 in
lemma IsParallelPair.left_ne [FiniteDimensional ℝ E] [Nontrivial E] {K F G : Set E} (h : IsParallelPair K F G)
    (hn : G.Nonempty) : F ≠ K := by
  intro he
  obtain ⟨x,hx⟩ := hn
  exact disjoint_left.mp h.2.2.1 (he.symm ▸ h.2.1.subset hx) hx

omit inst488 inst489 in
lemma IsMaximalProperFace.faceHull_vertex [FiniteDimensional ℝ E] [Nontrivial E] (_ : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsMaximalProperFace K F)
    {x : E} (hx : x ∈ K) (hxn : x ∉ F) :
    faceHull (closedBall (0:E) 1) ({x} ∪ F) = K := by
  let H := faceHull (closedBall (0:E) 1) ({x} ∪ F)
  have hbase : {x} ∪ F ⊆ K := union_subset (singleton_subset_iff.mpr hx) h.1.subset
  have hH := isFace_faceHull (convex_closedBall (0:E) 1) (hbase.trans hK.subset)
  have hHK : H ⊆ K := faceHull_min hK hbase
  have hFH : F ⊆ H := fun _ hx => subset_faceHull (Or.inr hx)
  by_contra hp
  have he := h.2.2 H (hH.mono hK.subset hHK) hFH hp
  exact hxn (he ▸ subset_faceHull (Or.inl (mem_singleton x)))

lemma IsMaximalProperFace.exchange (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsMaximalProperFace K F)
    (hpair : IsParallelPair K F G) (hn : F.Nonempty) {x y : E}
    (hx : x ∈ K.extremePoints ℝ) (hxG : x ∈ G)
    (hy : y ∈ K.extremePoints ℝ) (hyG : y ∈ G) :
    ∃ u ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ v ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ, x+u=y+v := by
  apply parallel_face_vertex_exchange hmed hK hpair hn hx hxG hy hyG
  rw [h.faceHull_vertex hmed hK hx.1 ((hpair.not_mem_iff hx).mpr hxG)]
  exact hy.1

lemma maximal_pair_of_disjoint (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K)
    (hF : IsMaximalProperFace K F) (hG : IsMaximalProperFace K G)
    (hFn : F.Nonempty) (_ : G.Nonempty) (hd : Disjoint F G) :
    IsParallelPair K F G := by
  obtain ⟨A,hA⟩ := maximal_proper_parallel hmed hK hF hFn
  have hGA : G ⊆ A := hA.subset_of_disjoint hmed hK hG.1 hd.symm
  have hAp : A ≠ K := hA.symm.left_ne hFn
  have he := hG.2.2 A hA.2.1 hGA hAp
  exact he ▸ hA

omit inst488 inst489 in
lemma proper_unit_face_subface_ne [FiniteDimensional ℝ E] [Nontrivial E] {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hFK : F ⊆ K) : F ≠ closedBall (0:E) 1 := by
  intro he
  exact hp (subset_antisymm hK.subset (he ▸ hFK))

lemma IsFace.rank_pos (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hp : F ≠ closedBall (0:E) 1)
    (hn : F.Nonempty) : 0 < faceRank F := by
  have hh := faceRank_lt hmed hF hp
    (show IsFace F ∅ from ⟨convex_empty,⟨empty_subset _,by simp⟩⟩) (Ne.symm hn.ne_empty)
  change Module.finrank ℝ (Submodule.span ℝ (∅ : Set E)) < faceRank F at hh
  rw [Submodule.span_empty] at hh
  simpa using hh

end

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma IsFace.of_support_le {K : Set E} (hK : Convex ℝ K)
    (f : E →ₗ[ℝ] ℝ) (c : ℝ) (hb : ∀ x ∈ K, f x ≤ c) :
    IsFace K {x ∈ K | f x = c} := by
  constructor
  · intro x hx y hy a b ha hb' hab
    refine ⟨hK hx.1 hy.1 ha hb' hab,?_⟩
    simp only [map_add,map_smul,smul_eq_mul,hx.2,hy.2]
    rw [← add_mul, hab, one_mul]
  · refine ⟨fun _ h => h.1,?_⟩
    intro x hx y hy z hz hs
    obtain ⟨a,b,ha,hb',hab,he⟩ := hs
    refine ⟨hx,?_⟩
    have hh := congrArg f he
    simp only [map_add,map_smul,smul_eq_mul,hz.2] at hh
    have hfx := hb x hx
    have hfy := hb y hy
    apply le_antisymm hfx
    by_contra hn
    have hlt : f x < c := lt_of_not_ge hn
    have hpos := mul_pos ha (sub_pos.mpr hlt)
    have hnon := mul_nonneg hb'.le (sub_nonneg.mpr hfy)
    have hc := congrArg (fun t : ℝ => t*c) hab
    nlinarith

variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma disjoint_faces_dual_vertex (hmed : HasMetricMedians E) {F G : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hG : IsFace (closedBall (0:E) 1) G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hd : Disjoint F G) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ x ∈ F, f x = 1) ∧ ∀ x ∈ G, f x = -1 := by
  obtain ⟨g,hg,hgF,hgG⟩ := disjoint_faces_opposite_support hmed hF.2 hG.2
    hF.1 hG.1 hFn hGn hd
  let A := F ∪ -G
  have hA : A ⊆ closedBall (0:E) 1 := by
    rintro x (hx | hx)
    · exact hF.subset hx
    · have hneg : -x ∈ G := hx
      have hh := hG.subset hneg
      simpa using hh
  have hD : {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | ∀ x ∈ A, f x = 1}.Nonempty := by
    refine ⟨g,mem_closedBall_zero_iff.mpr hg.le,?_⟩
    rintro x (hx | hx)
    · exact hgF x hx
    · have hh := hgG (-x) hx
      simp only [map_neg] at hh
      linarith
  obtain ⟨f,hf⟩ := (isCompact_dual_common A).extremePoints_nonempty hD
  refine ⟨f,(isFace_dual_common hA).2.extremePoints_subset_extremePoints hf,
    fun x hx => hf.1.2 x (Or.inl hx),?_⟩
  intro x hx
  have hh := hf.1.2 (-x) (Or.inr (by simpa using hx))
  simp only [map_neg] at hh
  linarith

lemma IsParallelPair.support_dual_vertex (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      F = {x ∈ K | f x = 1} ∧ G = {x ∈ K | f x = -1} := by
  obtain ⟨f,hf,hfF,hfG⟩ := disjoint_faces_dual_vertex hmed (hK.trans h.1)
    (hK.trans h.2.1) hFn hGn h.2.2.1
  have hp := parallelPair_of_dual_vertex hmed hK hf
  have hFsub : F ⊆ {x ∈ K | f x = 1} := fun x hx => ⟨h.1.subset hx,hfF x hx⟩
  have hGsub : G ⊆ {x ∈ K | f x = -1} := fun x hx => ⟨h.2.1.subset hx,hfG x hx⟩
  exact ⟨f,hf,subset_antisymm hFsub (h.symm.complement_anti hmed hK hp.symm hGsub),
    subset_antisymm hGsub (h.complement_anti hmed hK hp hFsub)⟩

lemma parallel_disjoint_union_face (hmed : HasMetricMedians E) {K F F' G G' : Set E}
    (hK : IsFace (closedBall (0:E) 1) K)
    (hF : IsParallelPair K F F') (hG : IsParallelPair K G G')
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hd : Disjoint F G) :
    IsFace K (convexHull ℝ (F ∪ G)) := by
  have hFG' := hG.subset_of_disjoint hmed hK hF.1 hd
  have hGF' := hF.subset_of_disjoint hmed hK hG.1 hd.symm
  obtain ⟨f,hf,heF,heF'⟩ := hF.support_dual_vertex hmed hK hFn (hGn.mono hGF')
  obtain ⟨g,hg,heG,heG'⟩ := hG.support_dual_vertex hmed hK hGn (hFn.mono hFG')
  have hb : ∀ x ∈ K, (f+g) x ≤ 0 := by
    have hs : K ⊆ {x | (f+g) x ≤ (0:ℝ)} := by
      apply hK.subset_of_vertices hmed
        (convex_halfSpace_le (f+g).toLinearMap.isLinear 0)
      intro x hx
      have hv := hK.extreme_mem hx.1 hx.2
      rcases hF.vertex_mem hv with hxF | hxF'
      · have hhF := (heF ▸ hxF).2
        have hhG := (heG' ▸ hFG' hxF).2
        change f x+g x ≤ 0
        linarith
      · have hhF := (heF' ▸ hxF').2
        have hhG := (dual_eval_bounds (mem_closedBall_zero_iff.mp hg.1) hx.1.1).2
        change f x+g x ≤ 0
        linarith
    exact fun x hx => hs hx
  have hC := IsFace.of_support_le hK.1 (f+g).toLinearMap 0 hb
  have he : convexHull ℝ (F ∪ G) = {x ∈ K | (f+g) x = 0} := by
    apply subset_antisymm
    · apply convexHull_min _ hC.1
      rintro x (hx | hx)
      · refine ⟨hF.1.subset hx,?_⟩
        have h1 := (heF ▸ hx).2
        have h2 := (heG' ▸ hFG' hx).2
        change f x+g x = 0
        linarith
      · refine ⟨hG.1.subset hx,?_⟩
        have h1 := (heG ▸ hx).2
        have h2 := (heF' ▸ hGF' hx).2
        change f x+g x = 0
        linarith
    · apply (hK.trans hC).subset_of_vertices hmed (convex_convexHull _ _)
      intro x hx
      apply subset_convexHull
      have hv := hK.extreme_mem hx.1 hx.2.1
      rcases hF.vertex_mem hv with hh | hh
      · exact Or.inl hh
      · right
        rcases hG.vertex_mem hv with hhG | hhG
        · exact hhG
        · have h1 := (heF' ▸ hh).2
          have h2 := (heG' ▸ hhG).2
          have h3 := hx.2.2
          change f x+g x = 0 at h3
          linarith
  exact he.symm ▸ hC

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Diamonds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Set Metric
namespace SymmetricMahler

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma IsParallelPair.square {K F G : Set E} (h : IsParallelPair K F G)
    {x y a b : E} (hx : x ∈ F) (hy : y ∈ G)
    (ha : a ∈ K.extremePoints ℝ) (hb : b ∈ K.extremePoints ℝ)
    (he : x+a=y+b) : a ∈ G ∧ b ∈ F := by
  constructor
  · apply (h.not_mem_iff ha).mp
    intro hh
    have hyF := (face_mem_of_parallelogram h.1 hx hh (h.2.1.subset hy) hb.1 he).1
    exact disjoint_left.mp h.2.2.1 hyF hy
  · apply (h.symm.not_mem_iff hb).mp
    intro hh
    have hxG := (face_mem_of_parallelogram h.2.1 hy hh (h.1.subset hx) ha.1 he.symm).1
    exact disjoint_left.mp h.2.2.1 hx hxG

lemma facial_diamond (hmed : HasMetricMedians E)
    {M H N N' P P' R R' Q Q' : Set E}
    (hM : IsFace (closedBall (0:E) 1) M) (hp : M ≠ closedBall (0:E) 1)
    (hN : IsMaximalProperFace M N) (hP : IsMaximalProperFace M P)
    (hR : IsMaximalProperFace M R)
    (pN : IsParallelPair M N N') (pP : IsParallelPair M P P')
    (pR : IsParallelPair M R R') (pQ : IsParallelPair M Q Q')
    (hH : H = N ∩ R') (hHP : H ⊆ P) (hHQ : H ⊆ Q)
    (hPRQ : P ∩ R ⊆ Q)
    {x y u v : E}
    (hx : x ∈ M.extremePoints ℝ) (hy : y ∈ M.extremePoints ℝ)
    (_ : u ∈ M.extremePoints ℝ) (hv : v ∈ M.extremePoints ℝ)
    (hxH : x ∈ H)
    (hyD : y ∈ R ∩ N' ∩ P' ∩ Q')
    (huD : u ∈ N ∩ P' ∩ Q)
    (hvD : v ∈ N' ∩ P ∩ Q')
    (he : x+y=u+v) :
    HasMFaceStructure (faceHull (closedBall (0:E) 1) ({y} ∪ H)) := by
  let T := faceHull (closedBall (0:E) 1) ({y} ∪ H)
  have hHb : IsFace (closedBall (0:E) 1) H := hH ▸ hM.trans (pN.1.inter pR.2.1)
  have hHM : H ⊆ M := fun z hz => pN.1.subset ((hH ▸ hz).1)
  have hbase : {y} ∪ H ⊆ M := union_subset (singleton_subset_iff.mpr hy.1) hHM
  have hT : IsFace (closedBall (0:E) 1) T :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hM.subset)
  have hTM : T ⊆ M := faceHull_min hM hbase
  have hTc : IsFace M T := hT.mono hM.subset hTM
  have hTp := proper_unit_face_subface_ne hM hp hTM
  have hHT : H ⊆ T := fun _ hz => subset_faceHull (Or.inr hz)
  have hyT : y ∈ T := subset_faceHull (Or.inl (mem_singleton _))
  have hxT := hHT hxH
  have hxNR := hH ▸ hxH
  have hNn : N.Nonempty := ⟨x,hxNR.1⟩
  have hPn : P.Nonempty := ⟨x,hHP hxH⟩
  have hRn : R.Nonempty := ⟨y,hyD.1.1.1⟩
  let A := N ∩ P' ∩ Q
  let B := N' ∩ P ∩ Q'
  have hA : IsFace M A := (pN.1.inter pP.2.1).inter pQ.1
  have hB : IsFace M B := (pN.2.1.inter pP.1).inter pQ.2.1
  have hBR : B ⊆ R' := by
    apply pR.subset_of_disjoint hmed hM hB
    exact disjoint_left.mpr (fun z hz hzR =>
      disjoint_left.mp pQ.2.2.1 (hPRQ ⟨hz.1.2,hzR⟩) hz.2)
  have hRP : R ∩ N' ∩ Q' ⊆ P' := by
    apply pP.subset_of_disjoint hmed hM ((pR.1.inter pN.2.1).inter pQ.2.1)
    exact disjoint_left.mpr (fun z hz hzP =>
      disjoint_left.mp pQ.2.2.1 (hPRQ ⟨hzP,hz.1.1⟩) hz.2)
  have hvR : v ∈ R' := hBR hvD
  have hAs : A ⊆ T ∩ R := by
    apply (hM.trans hA).subset_of_vertices hmed (hT.1.inter pR.1.1)
    intro t ht
    have htM := hM.extreme_mem ht.1 (hA.subset ht.2)
    obtain ⟨a,ha,b,hb,hab⟩ := hP.exchange hmed hM pP hPn htM ht.2.1.2 hy hyD.1.2
    have haM := hM.extreme_mem ha.2 (pP.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pP.1.subset hb.1)
    have hNa := pN.square ht.2.1.1 hyD.1.1.2 haM hbM hab
    have hQa := pQ.square ht.2.2 hyD.2 haM hbM hab
    have haR := hBR ⟨⟨hNa.1,ha.1⟩,hQa.1⟩
    have hRb := pR.square hyD.1.1.1 haR hbM htM
      (by simpa [add_comm] using hab.symm)
    have hbH : b ∈ H := hH.symm ▸ ⟨hNa.2,hRb.1⟩
    have htT := (face_mem_of_parallelogram hT hyT (hHT hbH)
      ht.1.1 ha.2.1 hab.symm).1
    exact ⟨htT,hRb.2⟩
  have hBs : B ⊆ T := by
    apply (hM.trans hB).subset_of_vertices hmed hT.1
    intro t ht
    have htM := hM.extreme_mem ht.1 (hB.subset ht.2)
    obtain ⟨a,ha,b,hb,hab⟩ := hN.exchange hmed hM pN hNn htM ht.2.1.1 hy hyD.1.1.2
    have haM := hM.extreme_mem ha.2 (pN.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pN.1.subset hb.1)
    have hRb := pR.symm.square (hBR ht.2) hyD.1.1.1 haM hbM hab
    have hbH : b ∈ H := hH.symm ▸ ⟨hb.1,hRb.2⟩
    exact (face_mem_of_parallelogram hT hyT (hHT hbH) ht.1.1 ha.2.1 hab.symm).1
  let U := faceHull (closedBall (0:E) 1) (A ∪ B)
  have hU : IsFace (closedBall (0:E) 1) U := isFace_faceHull (convex_closedBall _ _)
    ((union_subset hA.subset hB.subset).trans hM.subset)
  have hAU : A ⊆ U := fun _ hz => subset_faceHull (Or.inl hz)
  have hBU : B ⊆ U := fun _ hz => subset_faceHull (Or.inr hz)
  have hHU : H ⊆ U := by
    apply hHb.subset_of_vertices hmed hU.1
    intro t ht
    have htM := hM.extreme_mem ht.1 (hHM ht.2)
    have htNR := hH ▸ ht.2
    obtain ⟨a,ha,b,hb,hab⟩ := hR.exchange hmed hM pR hRn htM htNR.2 hv hvR
    have haM := hM.extreme_mem ha.2 (pR.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pR.1.subset hb.1)
    have hNa := pN.square htNR.1 hvD.1.1 haM hbM hab
    have hQa := pQ.square (hHQ ht.2) hvD.2 haM hbM hab
    have haP := hRP ⟨⟨ha.1,hNa.1⟩,hQa.1⟩
    have hbP := (pP.symm.square haP hvD.1.2 htM hbM
      (by simpa [add_comm] using hab)).2
    have hbA : b ∈ A := ⟨⟨hNa.2,hbP⟩,hQa.2⟩
    exact (face_mem_of_parallelogram hU (hBU hvD) (hAU hbA) ht.1.1 ha.2.1 hab.symm).1
  have hyU : y ∈ U := (face_mem_of_parallelogram hU (hAU huD) (hBU hvD)
    (hM.subset hx.1) (hM.subset hy.1) he.symm).2
  have hTU : T ⊆ U := faceHull_min hU
    (union_subset (singleton_subset_iff.mpr hyU) hHU)
  let V := faceHull (closedBall (0:E) 1) ({x} ∪ (T ∩ R))
  have hV : IsFace (closedBall (0:E) 1) V := isFace_faceHull (convex_closedBall _ _)
    ((union_subset (singleton_subset_iff.mpr hxT) inter_subset_left).trans hT.subset)
  have hxV : x ∈ V := subset_faceHull (Or.inl (mem_singleton _))
  have hTRV : T ∩ R ⊆ V := fun _ hz => subset_faceHull (Or.inr hz)
  have hAV : A ⊆ V := hAs.trans hTRV
  have hBV : B ⊆ V := by
    apply (hM.trans hB).subset_of_vertices hmed hV.1
    intro t ht
    have htM := hM.extreme_mem ht.1 (hB.subset ht.2)
    obtain ⟨a,ha,b,hb,hab⟩ := hR.exchange hmed hM pR hRn htM (hBR ht.2) hx hxNR.2
    have haM := hM.extreme_mem ha.2 (pR.1.subset ha.1)
    have hbM := hM.extreme_mem hb.2 (pR.1.subset hb.1)
    have hNa := pN.symm.square ht.2.1.1 hxNR.1 haM hbM hab
    have hQa := pQ.symm.square ht.2.2 (hHQ hxH) haM hbM hab
    have hbP := hRP ⟨⟨hb.1,hNa.2⟩,hQa.2⟩
    have haP := (pP.symm.square hbP ht.2.1.2 hx haM
      (by simpa [add_comm] using hab.symm)).2
    have haA : a ∈ A := ⟨⟨hNa.1,haP⟩,hQa.1⟩
    have hbT := (face_mem_of_parallelogram hT (hBs ht.2) (hAs haA).1
      (hM.subset hx.1) hb.2.1 hab).2
    exact (face_mem_of_parallelogram hV hxV (hTRV ⟨hbT,hb.1⟩)
      ht.1.1 ha.2.1 hab.symm).1
  have hUV : U ⊆ V := faceHull_min hV (union_subset hAV hBV)
  have hVT : V ⊆ T := faceHull_min hT
    (union_subset (singleton_subset_iff.mpr hxT) inter_subset_left)
  have hTV : T = V := subset_antisymm (hTU.trans hUV) hVT
  let W := faceHull (closedBall (0:E) 1) ({y} ∪ (T ∩ R'))
  have hTW : T = W := by
    apply subset_antisymm
    · exact faceHull_mono (union_subset_union Subset.rfl
        (fun z hz => ⟨hHT hz,(hH ▸ hz).2⟩))
    · exact faceHull_min hT
        (union_subset (singleton_subset_iff.mpr hyT) inter_subset_left)
  have pT := pR.restrict hmed hM hTc
  have hAn : (T ∩ R).Nonempty := ⟨y,hyT,hyD.1.1.1⟩
  have hBn : (T ∩ R').Nonempty := ⟨x,hxT,hxNR.2⟩
  have hrA := parallel_faceHull_rank hmed hT hTp pT hAn
    (hT.extreme_mem (hM.2.extremePoints_subset_extremePoints hx) hxT) ⟨hxT,hxNR.2⟩
  have hrB := parallel_faceHull_rank hmed hT hTp pT.symm hBn
    (hT.extreme_mem (hM.2.extremePoints_subset_extremePoints hy) hyT) ⟨hyT,hyD.1.1.1⟩
  change faceRank V = faceRank (T ∩ R) + 1 at hrA
  change faceRank W = faceRank (T ∩ R') + 1 at hrB
  rw [← hTV] at hrA
  rw [← hTW] at hrB
  exact ⟨T ∩ R,T ∩ R',rank_succ_maximal hmed hT hTp pT.1 (pT.left_ne hBn) hrA,
    rank_succ_maximal hmed hT hTp pT.2.1 (pT.symm.left_ne hAn) hrB,
    hAn,hBn,pT.2.2.1⟩

lemma maximal_mface_child_parallel (hmed : HasMetricMedians E) {M F F' G H : Set E}
    (hM : IsFace (closedBall (0:E) 1) M) (hp : M ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair M F F') (hmax : HasMaximalMRank F)
    (hG : IsMaximalProperFace F G) (hH : IsMaximalProperFace F H)
    (hGn : G.Nonempty) (hHn : H.Nonempty) (hGH : Disjoint G H) :
    IsParallelFace M H := by
  have hFball := hM.trans hpair.1
  have hFp := proper_unit_face_subface_ne hM hp hpair.1.subset
  have hGp := proper_unit_face_subface_ne hM hp (hG.1.subset.trans hpair.1.subset)
  have hHp := proper_unit_face_subface_ne hM hp (hH.1.subset.trans hpair.1.subset)
  have hFnh : F.Nonempty := hGn.mono hG.1.subset
  have hpairGH := maximal_pair_of_disjoint hmed hFball hG hH hGn hHn hGH
  obtain ⟨x,hx,hxH⟩ := (hFball.trans hH.1).exists_vertex hmed hHn
  have hxF := hH.1.subset hxH
  have hxM := hpair.1.subset hxF
  have hxG : x ∉ G := fun hh => disjoint_left.mp hGH hh hxH
  obtain ⟨S,hS,hGS,hxS⟩ := extend_face_avoiding_vertex hmed hM hp
    (hpair.1.trans hG.1) hGn (hM.extreme_mem hx hxM) hxG
  obtain ⟨S',hSS⟩ := maximal_proper_parallel hmed hM hS (hGn.mono hGS)
  have hxS' := (hSS.not_mem_iff (hM.extreme_mem hx hxM)).mp hxS
  have hFS : F ∩ S = G := by
    apply hG.2.2 _
    · exact (hpair.1.inter hS.1).mono hpair.1.subset inter_subset_left
    · exact fun _ hz => ⟨hG.1.subset hz,hGS hz⟩
    · intro he
      exact hxS ((he.symm ▸ hxF).2)
  have hFS' : F ∩ S' = H := by
    have hh := hSS.restrict hmed hM hpair.1
    rw [hFS] at hh
    exact hh.complement_unique hmed hFball hpairGH
  have hsub : S' ⊆ F := by
    by_contra hn
    obtain ⟨z,hz,hzS',hzF⟩ := (hM.trans hSS.2.1).exists_vertex_outside hmed hFball.1 hn
    have hzM := hSS.2.1.subset hzS'
    have hzF' := (hpair.not_mem_iff (hM.extreme_mem hz hzM)).mp hzF
    obtain ⟨a,ha,b,hb,he⟩ := hS.exchange hmed hM hSS (hGn.mono hGS)
      (hM.extreme_mem hx hxM) hxS' (hM.extreme_mem hz hzM) hzS'
    have haM := hS.1.subset ha.1
    have hbM := hS.1.subset hb.1
    have hbF : b ∈ F := by
      rcases hpair.vertex_mem (hM.extreme_mem hb.2 hbM) with hh | hh
      · exact hh
      · have hxF' := (face_mem_of_parallelogram hpair.2.1 hzF' hh hxM haM he.symm).1
        exact False.elim (disjoint_left.mp hpair.2.2.1 hxF hxF')
    have hbG : b ∈ G := hFS ▸ ⟨hbF,hb.1⟩
    have haF : a ∉ F := by
      intro hh
      have hzF' := (face_mem_of_parallelogram hpair.1 hxF hh hzM hbM he).1
      exact hzF hzF'
    let L := faceHull (closedBall (0:E) 1) ({z} ∪ F)
    have hbase : {z} ∪ F ⊆ M := union_subset (singleton_subset_iff.mpr hzM) hpair.1.subset
    have hL : IsFace (closedBall (0:E) 1) L :=
      isFace_faceHull (convex_closedBall _ _) (hbase.trans hM.subset)
    have hLM : L ⊆ M := faceHull_min hM hbase
    have hFL : F ⊆ L := fun _ hu => subset_faceHull (Or.inr hu)
    have hzL : z ∈ L := subset_faceHull (Or.inl (mem_singleton z))
    have hLp := proper_unit_face_subface_ne hM hp hLM
    have haL : a ∈ L := (face_mem_of_parallelogram hL hzL (hFL hbF)
      (hM.subset hxM) ha.2.1 he.symm).2
    have hLc : IsFace M L := hL.mono hM.subset hLM
    have hpL := hSS.restrict hmed hM hLc
    have hGA : G ⊆ L ∩ S := fun _ hu => ⟨hFL (hG.1.subset hu),hGS hu⟩
    have hHB : H ⊆ L ∩ S' := fun _ hu =>
      ⟨hFL (hH.1.subset hu),(hFS'.symm ▸ hu).2⟩
    have haA : a ∈ L ∩ S := ⟨haL,ha.1⟩
    have hzB : z ∈ L ∩ S' := ⟨hzL,hzS'⟩
    have hAn : (L ∩ S).Nonempty := hGn.mono hGA
    have hBn : (L ∩ S').Nonempty := hHn.mono hHB
    have hAp : L ∩ S ≠ L := hpL.left_ne hBn
    have hBp : L ∩ S' ≠ L := hpL.symm.left_ne hAn
    have hGAr := faceRank_lt hmed (hL.trans hpL.1)
      (proper_unit_face_subface_ne hL hLp hpL.1.subset)
      ((hFball.trans hG.1).mono (fun _ hz => hL.subset (hpL.1.subset hz)) hGA)
      (by intro hh; exact haF (hG.1.subset (hh.symm ▸ haA)))
    have hHBr := faceRank_lt hmed (hL.trans hpL.2.1)
      (proper_unit_face_subface_ne hL hLp hpL.2.1.subset)
      ((hFball.trans hH.1).mono (fun _ hz => hL.subset (hpL.2.1.subset hz)) hHB)
      (by intro hh; exact hzF (hH.1.subset (hh.symm ▸ hzB)))
    have hAr := faceRank_lt hmed hL hLp hpL.1 hAp
    have hBr := faceRank_lt hmed hL hLp hpL.2.1 hBp
    have hrG := maximal_proper_rank hmed hFball hFp hG hGn
    have hrH := maximal_proper_rank hmed hFball hFp hH hHn
    have hrL := parallel_faceHull_rank hmed hM hp hpair hFnh
      (hM.extreme_mem hz hzM) hzF'
    change faceRank L = faceRank F + 1 at hrL
    have hAm := rank_succ_maximal hmed hL hLp hpL.1 hAp (by omega)
    have hBm := rank_succ_maximal hmed hL hLp hpL.2.1 hBp (by omega)
    have hmL : HasMFaceStructure L :=
      ⟨L ∩ S,L ∩ S',hAm,hBm,hAn,hBn,hpL.2.2.1⟩
    have hbound := hmax L hL hLp hmL
    omega
  have he : S' = H := (inter_eq_right.mpr hsub).symm.trans hFS'
  exact ⟨S,he ▸ hSS.symm⟩

theorem maximal_mface_children_parallel (hmed : HasMetricMedians E) {M F F' G H : Set E}
    (hM : IsFace (closedBall (0:E) 1) M) (hp : M ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair M F F') (hmax : HasMaximalMRank F)
    (hG : IsMaximalProperFace F G) (hH : IsMaximalProperFace F H)
    (hGn : G.Nonempty) (hHn : H.Nonempty) (hGH : Disjoint G H) :
    IsParallelFace M G ∧ IsParallelFace M H :=
  ⟨maximal_mface_child_parallel hmed hM hp hpair hmax hH hG hHn hGn hGH.symm,
    maximal_mface_child_parallel hmed hM hp hpair hmax hG hH hGn hHn hGH⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst504 : FiniteDimensional ℝ E] [inst505 : Nontrivial E]

omit inst504 inst505 in
lemma IsParallelFace.refl [FiniteDimensional ℝ E] [Nontrivial E] {K : Set E} (hK : Convex ℝ K) : IsParallelFace K K :=
  ⟨∅,IsFace.refl hK,IsFace.empty K,by simp,by simp [hK.convexHull_eq]⟩

lemma IsParallelPair.square_sides {K F G : Set E} (h : IsParallelPair K F G)
    {x y u v : E} (hx : x ∈ F) (hy : y ∈ G)
    (hu : u ∈ K.extremePoints ℝ) (hv : v ∈ K.extremePoints ℝ)
    (he : x+y=u+v) : (u ∈ F ∧ v ∈ G) ∨ (v ∈ F ∧ u ∈ G) := by
  rcases h.vertex_mem hu with hh | hh
  · left
    refine ⟨hh,(h.not_mem_iff hv).mp ?_⟩
    intro hvF
    exact disjoint_left.mp h.2.2.1
      (face_mem_of_parallelogram h.1 hh hvF (h.1.subset hx) (h.2.1.subset hy) he.symm).2 hy
  · right
    refine ⟨(h.symm.not_mem_iff hv).mp ?_,hh⟩
    intro hvG
    exact disjoint_left.mp h.2.2.1 hx
      (face_mem_of_parallelogram h.2.1 hh hvG (h.1.subset hx) (h.2.1.subset hy) he.symm).1

theorem maximal_mface_parallel (hmed : HasMetricMedians E) {K F : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hmF : HasMFaceStructure F) (hmax : HasMaximalMRank F) :
    IsParallelFace K F := by
  classical
  by_contra hn
  have hFb := hK.trans hF
  have hFp := proper_unit_face_subface_ne hK hp hF.subset
  have hFn : F.Nonempty := by
    obtain ⟨G,H,hG,-,hGn,-⟩ := hmF
    exact hGn.mono hG.1.subset
  let D : Set (Set E) := {M | IsFace (closedBall (0:E) 1) M ∧ M ⊆ K ∧ F ⊆ M ∧
    ¬ IsParallelFace M F}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset (fun _ h => h.1)
  obtain ⟨M,hmin⟩ := hDf.exists_minimal ⟨K,hK,Subset.rfl,hF.subset,hn⟩
  obtain ⟨hM,hMK,hFM,hnM⟩ := hmin.1
  have hMp := proper_unit_face_subface_ne hK hp hMK
  have hFc : IsFace M F := hFb.mono hM.subset hFM
  have hFMne : F ≠ M := by
    intro hh
    rw [hh] at hnM
    exact hnM (IsParallelFace.refl hM.1)
  have hsmall : ∀ N, IsFace M N → F ⊆ N → N ≠ M → IsParallelFace N F := by
    intro N hN hFN hnp
    by_contra hnN
    have hND : N ∈ D := ⟨hM.trans hN,hN.subset.trans hMK,hFN,hnN⟩
    exact hnp (subset_antisymm hN.subset (hmin.2 hND hN.subset))
  obtain ⟨x,hx,y,hy,u0,hu0,v0,hv0,he0⟩ := nonparallel_vertex_parallelogram hmed hM hFc hFn hFMne hnM
  have hxM := hM.extreme_mem hx.2 (hFM hx.1)
  have hyM := hM.extreme_mem hy.2 hy.1.1
  have hu0M := hM.extreme_mem hu0.2 hu0.1.1
  have hv0M := hM.extreme_mem hv0.2 hv0.1.1
  have hjoin : faceHull (closedBall (0:E) 1) ({y} ∪ F) = M := by
    let J := faceHull (closedBall (0:E) 1) ({y} ∪ F)
    have hbase : {y} ∪ F ⊆ M := union_subset (singleton_subset_iff.mpr hy.1.1) hFM
    have hJ : IsFace (closedBall (0:E) 1) J :=
      isFace_faceHull (convex_closedBall _ _) (hbase.trans hM.subset)
    have hJM : J ⊆ M := faceHull_min hM hbase
    have hFJ : F ⊆ J := fun _ hz => subset_faceHull (Or.inr hz)
    have hyJ : y ∈ J := subset_faceHull (Or.inl (mem_singleton _))
    have huv := face_mem_of_parallelogram hJ (hFJ hx.1) hyJ hu0.2.1 hv0.2.1 he0
    have hnJ := parallelogram_not_parallel hx.1 (hFJ hx.1) hyJ
      (hJ.extreme_mem hu0.2 huv.1) (hJ.extreme_mem hv0.2 huv.2) hu0.1.2 hv0.1.2 he0
    exact subset_antisymm hJM (hmin.2 ⟨hJ,hJM.trans hMK,hFJ,hnJ⟩ hJM)
  obtain ⟨N,hN,hFN,hyN⟩ := extend_face_avoiding_vertex hmed hM hMp hFc hFn hyM hy.1.2
  obtain ⟨N',pN⟩ := maximal_proper_parallel hmed hM hN (hFn.mono hFN)
  have hyN' := (pN.not_mem_iff hyM).mp hyN
  obtain ⟨u,hu,v,hv,he,huN,hvN'⟩ :
      ∃ u ∈ (M \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
        ∃ v ∈ (M \ F) ∩ (closedBall (0:E) 1).extremePoints ℝ,
          x+y=u+v ∧ u ∈ N ∧ v ∈ N' := by
    rcases pN.square_sides (hFN hx.1) hyN' hu0M hv0M he0 with hh | hh
    · exact ⟨u0,hu0,v0,hv0,he0,hh.1,hh.2⟩
    · exact ⟨v0,hv0,u0,hu0,by simpa [add_comm] using he0,hh.1,hh.2⟩
  have huM := hM.extreme_mem hu.2 hu.1.1
  have hvM := hM.extreme_mem hv.2 hv.1.1
  obtain ⟨P,hP,hFP,huP⟩ := extend_face_avoiding_vertex hmed hM hMp hFc hFn huM hu.1.2
  obtain ⟨P',pP⟩ := maximal_proper_parallel hmed hM hP (hFn.mono hFP)
  have huP' := (pP.not_mem_iff huM).mp huP
  have hpys := pP.square (hFP hx.1) huP' hyM hvM he
  have hyP' : y ∈ P' := hpys.1
  have hvP : v ∈ P := hpys.2
  obtain ⟨G,H,hG,hH,hGn,hHn,hGH,hxH⟩ :
      ∃ G H, IsMaximalProperFace F G ∧ IsMaximalProperFace F H ∧
        G.Nonempty ∧ H.Nonempty ∧ Disjoint G H ∧ x ∈ H := by
    obtain ⟨G,H,hG,hH,hGn,hHn,hGH⟩ := hmF
    have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
    rcases pGH.vertex_mem (hFb.extreme_mem hx.2 hx.1) with hh | hh
    · exact ⟨H,G,hH,hG,hHn,hGn,hGH.symm,hh⟩
    · exact ⟨G,H,hG,hH,hGn,hHn,hGH,hh⟩
  have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
  obtain ⟨O,pFO⟩ := hsmall P hP.1 hFP hP.2.1
  obtain ⟨C,pFC⟩ := hsmall N hN.1 hFN hN.2.1
  obtain ⟨S,pHS⟩ := (maximal_mface_children_parallel hmed (hM.trans hN.1)
    (proper_unit_face_subface_ne hM hMp hN.1.subset) pFC hmax hG hH hGn hHn hGH).2
  obtain ⟨I,pHI⟩ := (maximal_mface_children_parallel hmed (hM.trans hP.1)
    (proper_unit_face_subface_ne hM hMp hP.1.subset) pFO hmax hG hH hGn hHn hGH).2
  have hGS : G ⊆ S := pHS.subset_of_disjoint hmed (hM.trans hN.1)
    ((hFb.trans hG.1).mono (hM.trans hN.1).subset (hG.1.subset.trans hFN)) hGH
  have hxS : x ∉ S := fun hh => disjoint_left.mp pHS.2.2.1 hxH hh
  obtain ⟨R,hR,hSR,hxR⟩ := extend_face_avoiding_vertex hmed hM hMp
    (hN.1.trans pHS.2.1) (hGn.mono hGS) hxM hxS
  obtain ⟨R',pR⟩ := maximal_proper_parallel hmed hM hR (hGn.mono (hGS.trans hSR))
  have hxR' := (pR.not_mem_iff hxM).mp hxR
  have hFR : F ∩ R = G := hG.2.2 _
    ((hFc.inter hR.1).mono hFM inter_subset_left)
    (fun _ hz => ⟨hG.1.subset hz,hSR (hGS hz)⟩)
    (by intro hh; exact hxR ((hh.symm ▸ hx.1).2))
  have hNR : N ∩ R = S := by
    apply subset_antisymm
    · apply pHS.subset_of_disjoint hmed (hM.trans hN.1)
        ((hN.1.inter hR.1).mono hN.1.subset inter_subset_left)
      apply disjoint_left.mpr
      intro z hz hzH
      exact disjoint_left.mp hGH (hFR ▸ ⟨hH.1.subset hzH,hz.2⟩) hzH
    · exact fun z hz => ⟨pHS.2.1.subset hz,hSR hz⟩
  have hNR' : N ∩ R' = H := by
    have hh := pR.restrict hmed hM hN.1
    rw [hNR] at hh
    exact hh.complement_unique hmed (hM.trans hN.1) pHS.symm
  have huS : u ∈ S := (pHS.not_mem_iff ((hM.trans hN.1).extreme_mem hu.2 huN)).mp
    (fun hh => hu.1.2 (hH.1.subset hh))
  have huR := hSR huS
  have hrys := pR.symm.square hxR' huR hyM hvM he
  have hyR := hrys.1
  have hvR' := hrys.2
  have hHdis : Disjoint H (P ∩ R) := disjoint_left.mpr (fun z hz hzPR =>
    disjoint_left.mp pR.2.2.1 hzPR.2 ((hNR'.symm ▸ hz).2))
  have pPR := pR.restrict hmed hM hP.1
  have hPRn : (P ∩ R).Nonempty := hGn.mono
    (fun z hz => ⟨hFP (hG.1.subset hz),hSR (hGS hz)⟩)
  let J := convexHull ℝ (H ∪ (P ∩ R))
  have hJc : IsFace P J := parallel_disjoint_union_face hmed (hM.trans hP.1)
    pHI pPR hHn hPRn hHdis
  have hJ := (hM.trans hP.1).trans hJc
  have hFJ : F ⊆ J := by
    rw [pGH.2.2.2]
    exact convexHull_mono (union_subset
      (fun z hz => Or.inr ⟨hFP (hG.1.subset hz),hSR (hGS hz)⟩)
      (fun _ hz => Or.inl hz))
  let Z := O ∩ R'
  have hZ : IsFace (closedBall (0:E) 1) Z :=
    ((hM.trans hP.1).trans pFO.2.1).inter (hM.trans pR.2.1)
  have hvO := (pFO.not_mem_iff ((hM.trans hP.1).extreme_mem hv.2 hvP)).mp hv.1.2
  have hvZ : v ∈ Z := ⟨hvO,hvR'⟩
  have hJZ : Disjoint J Z := by
    by_contra hd
    have hn : (J ∩ Z).Nonempty := not_disjoint_iff.mp hd
    obtain ⟨z,hz,hzJ,hzZ⟩ := (hJ.inter hZ).exists_vertex hmed hn
    have hzV := hJ.extreme_mem hz hzJ
    change z ∈ (convexHull ℝ (H ∪ (P ∩ R))).extremePoints ℝ at hzV
    rcases extremePoints_convexHull_subset hzV with hh | hh
    · exact disjoint_left.mp pFO.2.2.1 (hH.1.subset hh) hzZ.1
    · exact disjoint_left.mp pR.2.2.1 hh.2 hzZ.2
  obtain ⟨q,hq,hqJ,hqZ⟩ := disjoint_faces_dual_vertex hmed hJ hZ
    (hFn.mono hFJ) ⟨v,hvZ⟩ hJZ
  let Q := {z ∈ M | q z = 1}
  let Q' := {z ∈ M | q z = -1}
  have pQ : IsParallelPair M Q Q' := parallelPair_of_dual_vertex hmed hM hq
  have hFQ : F ⊆ Q := fun z hz => ⟨hFM hz,hqJ z (hFJ hz)⟩
  have hPRQ : P ∩ R ⊆ Q := fun z hz =>
    ⟨hP.1.subset hz.1,hqJ z (subset_convexHull ℝ _ (Or.inr hz))⟩
  have hvQ' : v ∈ Q' := ⟨hv.1.1,hqZ v hvZ⟩
  have hqys := pQ.square (hFQ hx.1) hvQ' hyM huM (by simpa [add_comm] using he)
  have hyQ' := hqys.1
  have huQ := hqys.2
  let T := faceHull (closedBall (0:E) 1) ({y} ∪ H)
  have hmT : HasMFaceStructure T := facial_diamond hmed hM hMp hN hP hR pN pP pR pQ
    hNR'.symm (hH.1.subset.trans hFP) (hH.1.subset.trans hFQ) hPRQ
    hxM hyM huM hvM hxH ⟨⟨⟨hyR,hyN'⟩,hyP'⟩,hyQ'⟩
    ⟨⟨huN,huP'⟩,huQ⟩ ⟨⟨hvN',hvP⟩,hvQ'⟩ he
  have hbaseT : {y} ∪ H ⊆ M := union_subset (singleton_subset_iff.mpr hy.1.1)
    (hH.1.subset.trans hFM)
  have hT : IsFace (closedBall (0:E) 1) T :=
    isFace_faceHull (convex_closedBall _ _) (hbaseT.trans hM.subset)
  have hTM : T ⊆ M := faceHull_min hM hbaseT
  have hTp := proper_unit_face_subface_ne hM hMp hTM
  have hHT : H ⊆ T := fun _ hz => subset_faceHull (Or.inr hz)
  have hyT : y ∈ T := subset_faceHull (Or.inl (mem_singleton _))
  have huT := (face_mem_of_parallelogram hT (hHT hxH) hyT hu.2.1 hv.2.1 he).1
  have hTN : IsFace (closedBall (0:E) 1) (T ∩ N) := hT.inter (hM.trans hN.1)
  have hHTN : H ⊆ T ∩ N := fun z hz => ⟨hHT hz,hFN (hH.1.subset hz)⟩
  have hr1 := faceRank_lt hmed hTN
    (proper_unit_face_subface_ne hT hTp inter_subset_left)
    ((hFb.trans hH.1).mono hTN.subset hHTN)
    (by intro hh; exact hu.1.2 (hH.1.subset (hh.symm ▸ ⟨huT,huN⟩)))
  have hr2 := faceRank_lt hmed hT hTp (hTN.mono hT.subset inter_subset_left)
    (by intro hh; exact hyN ((hh.symm ▸ hyT).2))
  have hrH := maximal_proper_rank hmed hFb hFp hH hHn
  have hrT := hmax T hT hTp hmT
  omega

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst508 : FiniteDimensional ℝ E] [inst509 : Nontrivial E]

lemma IsFace.exists_generator (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty) :
    ∃ x ∈ F, faceHull (closedBall (0:E) 1) {x} = F := by
  classical
  let D : Set (Set E) := {G | ∃ x ∈ F, G = faceHull (closedBall (0:E) 1) {x}}
  have hf : D.Finite := (finite_unit_faces_of_medians hmed).subset (by
    rintro G ⟨x,hx,rfl⟩
    exact isFace_faceHull (convex_closedBall _ _) (singleton_subset_iff.mpr (hF.subset hx)))
  obtain ⟨x0,hx0⟩ := hn
  obtain ⟨G,hmax⟩ := hf.exists_maximal ⟨_,x0,hx0,rfl⟩
  obtain ⟨x,hx,rfl⟩ := hmax.1
  refine ⟨x,hx,subset_antisymm (faceHull_min hF (singleton_subset_iff.mpr hx)) ?_⟩
  intro y hy
  let z := (1/2:ℝ) • x+(1/2:ℝ) • y
  have hz : z ∈ F := hF.1 hx hy (by norm_num) (by norm_num) (by norm_num)
  have hZ := isFace_faceHull (convex_closedBall (0:E) 1)
    (singleton_subset_iff.mpr (hF.subset hz))
  have hseg : z ∈ openSegment ℝ x y := ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  have hzZ : z ∈ faceHull (closedBall (0:E) 1) {z} := subset_faceHull (mem_singleton z)
  have hxZ := hZ.2.left_mem_of_mem_openSegment (hF.subset hx) (hF.subset hy) hzZ hseg
  have hyZ := hZ.2.right_mem_of_mem_openSegment (hF.subset hx) (hF.subset hy) hzZ hseg
  exact hmax.2 ⟨z,hz,rfl⟩ (faceHull_min hZ (singleton_subset_iff.mpr hxZ)) hyZ

omit inst508 inst509 in
lemma faceHull_midpoint_eq [FiniteDimensional ℝ E] [Nontrivial E] {K : Set E} (hK : Convex ℝ K) {x y : E}
    (hx : x ∈ K) (hy : y ∈ K) :
    faceHull K {(1/2:ℝ) • x+(1/2:ℝ) • y} = faceHull K ({x} ∪ {y}) := by
  have hJ := isFace_faceHull hK (union_subset (singleton_subset_iff.mpr hx) (singleton_subset_iff.mpr hy))
  have hm := hK hx hy (show (0:ℝ) ≤ 1/2 by norm_num) (show (0:ℝ) ≤ 1/2 by norm_num) (by norm_num)
  have hL := isFace_faceHull hK (singleton_subset_iff.mpr hm)
  have hxJ : x ∈ faceHull K ({x} ∪ {y}) := subset_faceHull (Or.inl (mem_singleton x))
  have hyJ : y ∈ faceHull K ({x} ∪ {y}) := subset_faceHull (Or.inr (mem_singleton y))
  have hmL : (1/2:ℝ) • x+(1/2:ℝ) • y ∈ faceHull K {(1/2:ℝ) • x+(1/2:ℝ) • y} :=
    subset_faceHull (mem_singleton _)
  have hs : (1/2:ℝ) • x+(1/2:ℝ) • y ∈ openSegment ℝ x y :=
    ⟨1/2,1/2,by norm_num,by norm_num,by norm_num,rfl⟩
  exact subset_antisymm (faceHull_min hJ (singleton_subset_iff.mpr
    (hJ.1 hxJ hyJ (by norm_num) (by norm_num) (by norm_num))))
    (faceHull_min hL (union_subset
      (singleton_subset_iff.mpr (hL.2.left_mem_of_mem_openSegment hx hy hmL hs))
      (singleton_subset_iff.mpr (hL.2.right_mem_of_mem_openSegment hx hy hmL hs))))

lemma IsFace.exposed_generator (hmed : HasMetricMedians E) {F : Set E}
    (hF : IsFace (closedBall (0:E) 1) F) (hn : F.Nonempty)
    (hp : F ≠ closedBall (0:E) 1) :
    ∃ f : E →L[ℝ] ℝ, ‖f‖ ≤ 1 ∧ F = {x ∈ closedBall (0:E) 1 | f x = 1} := by
  classical
  let V := (closedBall (0:E) 1).extremePoints ℝ \ F
  have hVf : V.Finite := (finite_extreme_unit_of_medians hmed).subset sdiff_subset
  have hVn : V.Nonempty := by
    obtain ⟨x,hx,hxb,hxf⟩ := (IsFace.refl (convex_closedBall (0:E) 1)).exists_vertex_outside hmed hF.1
      (by intro hs; exact hp (subset_antisymm hF.subset hs))
    exact ⟨x,hx,hxf⟩
  have hsep : ∀ x : V, ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ y ∈ F, f y = 1) ∧ f x = -1 := fun x => face_vertex_dual_separation hmed hF hn x.2.1 x.2.2
  choose f hf hfF hfx using hsep
  let : Fintype V := hVf.fintype
  let : Nonempty V := hVn.to_subtype
  let c : ℝ := Fintype.card V
  have hc : 0 < c := by
    change 0 < (Fintype.card V : ℝ)
    exact_mod_cast (Fintype.card_pos (α := V))
  let g : E →L[ℝ] ℝ := c⁻¹ • ∑ x : V, f x
  have hg : ‖g‖ ≤ 1 := by
    calc
      ‖g‖ = c⁻¹ * ‖∑ x : V, f x‖ := by simp [g,norm_smul,abs_of_pos hc]
      _ ≤ c⁻¹ * ∑ x : V, ‖f x‖ := mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hc.le)
      _ ≤ c⁻¹ * ∑ _x : V, (1:ℝ) := mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum (fun x _ => mem_closedBall_zero_iff.mp (hf x).1)) (inv_nonneg.mpr hc.le)
      _ = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        exact inv_mul_cancel₀ (ne_of_gt hc)
  have hge : ∀ x ∈ closedBall (0:E) 1, g x = 1 ↔ ∀ v : V, f v x = 1 := by
    intro x hx
    have he : g x = c⁻¹ * ∑ v : V, f v x := by simp [g]
    rw [he]
    constructor
    · intro hgx v
      have hsum : ∑ v : V, f v x = c := by
        have ht := congrArg (fun a : ℝ => c*a) hgx
        simpa [← mul_assoc,ne_of_gt hc] using ht
      have heq : ∑ v : V, f v x = ∑ _v : V, (1:ℝ) := by simpa [c] using hsum
      exact (Finset.sum_eq_sum_iff_of_le (fun v _ =>
        (dual_eval_bounds (mem_closedBall_zero_iff.mp (hf v).1) hx).2)).mp heq v (Finset.mem_univ v)
    · intro hh
      simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
      exact inv_mul_cancel₀ (ne_of_gt hc)
  refine ⟨g,hg,subset_antisymm (fun x hx => ⟨hF.subset hx,(hge x (hF.subset hx)).mpr
    (fun v => hfF v x hx)⟩) ?_⟩
  apply (isFace_support hg).subset_of_vertices hmed hF.1
  intro x hx
  by_contra hxn
  have hh := (hge x hx.2.1).mp hx.2.2 ⟨x,hx.1,hxn⟩
  have hm := hfx ⟨x,hx.1,hxn⟩
  linarith

lemma faceHull_radial (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {w y : E} (hw : w ∈ closedBall (0:E) 1)
    (hy : y ∈ faceHull (closedBall (0:E) 1) {w}) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ ∃ z ∈ closedBall (0:E) 1,
      w = a • y+(1-a) • z := by
  classical
  have hyB := faceHull_min (IsFace.refl (convex_closedBall (0:E) 1))
    (singleton_subset_iff.mpr hw) hy
  let D := (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ
  have hDf : D.Finite := finite_extreme_unit_of_medians hdual
  let S : Set ℝ := {1} ∪ ((fun f : E →L[ℝ] ℝ => (1-f w)/2) '' {f ∈ D | f w < 1})
  have hSf : S.Finite := (finite_singleton 1).union
    ((hDf.subset (fun _ h => h.1)).image _)
  have hSn : S.Nonempty := ⟨1,Or.inl (mem_singleton _)⟩
  obtain ⟨r,hr⟩ := hSf.exists_minimal hSn
  have hrmin : ∀ s ∈ S, r ≤ s := fun s hs => le_of_not_gt (fun hh => not_lt_of_ge (hr.2 hs hh.le) hh)
  have hrS := hr.1
  have hrpos : 0 < r := by
    rcases hrS with hr | ⟨f,⟨hf,hfw⟩,rfl⟩
    · simp only [mem_singleton_iff] at hr
      linarith
    · linarith
  let a := r/2
  have ha : 0 < a := by dsimp [a]; linarith
  have ha1 : a < 1 := by have hh := hrmin 1 (Or.inl (mem_singleton _)); dsimp [a]; linarith
  let z : E := (1-a)⁻¹ • (w-a • y)
  have hz : z ∈ closedBall (0:E) 1 := by
    apply mem_closedBall_zero_iff.mpr
    apply norm_le_of_dual_extreme_le
    intro f hf
    have hfw := (dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hw).2
    have hfy := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) hyB
    have hm : f w-a*f y ≤ 1-a := by
      by_cases he : f w = 1
      · have hyf := faceHull_min (isFace_support (mem_closedBall_zero_iff.mp hf.1))
          (singleton_subset_iff.mpr ⟨hw,he⟩) hy
        rw [he,hyf.2]
        ring_nf
        exact le_rfl
      · have hh := hrmin ((1-f w)/2) (Or.inr ⟨f,⟨hf,lt_of_le_of_ne hfw he⟩,rfl⟩)
        have hn := mul_nonneg ha.le (show 0 ≤ f y+1 by linarith)
        dsimp [a] at *
        nlinarith
    change f ((1-a)⁻¹ • (w-a • y)) ≤ 1
    simp only [map_smul,map_sub,smul_eq_mul]
    exact (inv_mul_le_iff₀ (sub_pos.mpr ha1)).mpr (by simpa using hm)
  refine ⟨a,ha,ha1,z,hz,?_⟩
  dsimp [z]
  rw [smul_smul,mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr ha1)),one_smul]
  abel

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst512 : FiniteDimensional ℝ E]

omit inst512 in
lemma LinearIsometryEquiv.image_extreme_unit [FiniteDimensional ℝ E] {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (e : E ≃ₗᵢ[ℝ] F) :
    e '' (closedBall (0:E) 1).extremePoints ℝ = (closedBall (0:F) 1).extremePoints ℝ := by
  rw [image_extremePoints,LinearIsometryEquiv.image_closedBall,map_zero]

lemma extreme_unit_neg {x : E} (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ) :
    -x ∈ (closedBall (0:E) 1).extremePoints ℝ := by
  have he := LinearIsometryEquiv.image_extreme_unit (LinearIsometryEquiv.neg ℝ (E:=E))
  rw [← he]
  exact ⟨x,hx,rfl⟩

variable [Nontrivial E]

lemma dual_disjoint_faces_primal_vertex (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {F G : Set (E →L[ℝ] ℝ)}
    (hF : IsFace (closedBall (0 : E →L[ℝ] ℝ) 1) F)
    (hG : IsFace (closedBall (0 : E →L[ℝ] ℝ) 1) G)
    (hFn : F.Nonempty) (hGn : G.Nonempty) (hd : Disjoint F G) :
    ∃ x ∈ (closedBall (0:E) 1).extremePoints ℝ,
      (∀ f ∈ F, f x = 1) ∧ ∀ g ∈ G, g x = -1 := by
  obtain ⟨u,hu,huF,huG⟩ := disjoint_faces_dual_vertex hdual hF hG hFn hGn hd
  rw [← LinearIsometryEquiv.image_extreme_unit (finiteBidual (E:=E))] at hu
  obtain ⟨x,hx,rfl⟩ := hu
  exact ⟨x,hx,huF,huG⟩

lemma IsParallelPair.square_points (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (h : IsParallelPair K F G)
    {x y a b : E} (hx : x ∈ F) (hy : y ∈ G) (ha : a ∈ K) (hb : b ∈ K)
    (he : x+a=y+b) : a ∈ G ∧ b ∈ F := by
  obtain ⟨f,hf,heF,heG⟩ := h.support_dual_vertex hmed hK ⟨x,hx⟩ ⟨y,hy⟩
  have hfx := (heF ▸ hx).2
  have hfy := (heG ▸ hy).2
  have hfa := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) (hK.subset ha)
  have hfb := dual_eval_bounds (mem_closedBall_zero_iff.mp hf.1) (hK.subset hb)
  have hh := congrArg f he
  simp only [map_add,hfx,hfy] at hh
  exact ⟨heG.symm ▸ ⟨ha,by linarith⟩,heF.symm ▸ ⟨hb,by linarith⟩⟩

lemma maximal_unit_face_support (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty) :
    ∃ f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      K = {x ∈ closedBall (0:E) 1 | f x = 1} := by
  obtain ⟨f,hf,hfK⟩ := proper_face_support hmed hK.1 hn hK.2.1
  refine ⟨f,hf,?_⟩
  apply Eq.symm
  apply hK.2.2 _ (isFace_support (mem_closedBall_zero_iff.mp hf.1))
    (fun x hx => ⟨hK.1.subset hx,hfK x hx⟩)
  intro hh
  have h0 : (0:E) ∈ {x ∈ closedBall (0:E) 1 | f x = 1} := hh.symm ▸ (by simp)
  simpa using h0.2

lemma dual_vertex_maximal_support (hmed : HasMetricMedians E) {f : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ) :
    IsMaximalProperFace (closedBall (0:E) 1) {x ∈ closedBall (0:E) 1 | f x = 1} := by
  apply full_rank_maximal_proper hmed (isFace_support (mem_closedBall_zero_iff.mp hf.1))
  · intro hh
    have h0 : (0:E) ∈ {x ∈ closedBall (0:E) 1 | f x = 1} := hh.symm ▸ (by simp)
    simpa using h0.2
  · unfold faceRank
    rw [span_support_dual_vertex hmed hf,finrank_top]

lemma vertex_in_two_vertex_face (hmed : HasMetricMedians E) {a b c : E}
    (ha : a ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hb : b ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hc : c ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hcJ : c ∈ faceHull (closedBall (0:E) 1) ({a} ∪ {b})) :
    ∃ d ∈ (closedBall (0:E) 1).extremePoints ℝ, a+b=c+d := by
  obtain ⟨u,hu,d,hd,he⟩ := face_vertex_exchange hmed ha hc
    ⟨convex_singleton b,isExtreme_singleton.mpr hb⟩ (singleton_nonempty b) hcJ
  have huB : u=b := hu.1
  exact ⟨d,hd,huB ▸ he⟩

end SymmetricMahler

open Set Metric
namespace SymmetricMahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst516 : FiniteDimensional ℝ E] [inst517 : Nontrivial E]

omit inst516 inst517 in
lemma disjoint_span_insert [FiniteDimensional ℝ E] [Nontrivial E] (A S V : Submodule ℝ E) {y : E}
    (hAS : Disjoint A S) (hAV : A ≤ V) (hSV : S ≤ V) (hy : y ∉ V) :
    Disjoint A (Submodule.span ℝ ({y} : Set E) ⊔ S) := by
  rw [Submodule.disjoint_def]
  intro z hzA hz
  obtain ⟨t,ht,s,hs,rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a,rfl⟩ := Submodule.mem_span_singleton.mp ht
  have hay : a • y ∈ V := by
    convert V.sub_mem (hAV hzA) (hSV hs) using 1 ; abel
  have ha : a = 0 := by
    by_contra hn
    exact hy ((Submodule.smul_mem_iff V hn).mp hay)
  simp only [ha,zero_smul,zero_add] at hzA ⊢
  exact Submodule.disjoint_def.mp hAS s hzA hs

theorem split_of_no_vertex_parallelogram (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G)
    (hn : ∀ x ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∀ z ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∀ y ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∀ w ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ, x+y=z+w → x=z) :
    Disjoint (Submodule.span ℝ F) (Submodule.span ℝ G) := by
  classical
  generalize hr : faceRank K = r
  induction r using Nat.strong_induction_on generalizing K F G with
  | h r ih =>
    by_cases hFn : F.Nonempty
    · by_cases hGn : G.Nonempty
      · obtain ⟨y,hy,hyG⟩ := (hK.trans hpair.2.1).exists_vertex hmed hGn
        have hyK := hK.extreme_mem hy (hpair.2.1.subset hyG)
        have hyF := (hpair.not_mem_iff hyK).mpr hyG
        obtain ⟨H,hH,hFH,hyH⟩ := extend_face_avoiding_vertex hmed hK hp hpair.1 hFn hyK hyF
        obtain ⟨H',hHH⟩ := maximal_proper_parallel hmed hK hH (hFn.mono hFH)
        have hHr := faceRank_lt hmed hK hp hH.1 hH.2.1
        have hHball := hK.trans hH.1
        have hHp := proper_unit_face_subface_ne hK hp hH.1.subset
        have hFGH : IsParallelPair H F (H ∩ G) := by
          have hh := hpair.restrict hmed hK hH.1
          have he : H ∩ F = F := inter_eq_right.mpr hFH
          rwa [he] at hh
        have hdis : Disjoint (Submodule.span ℝ F) (Submodule.span ℝ (H ∩ G)) := by
          apply ih (faceRank H) (by omega) hHball hHp hFGH
          · intro x hx z hz a ha b hb he
            exact hn x hx z hz a ⟨ha.1.2,ha.2⟩ b ⟨hb.1.2,hb.2⟩ he
          · rfl
        have hspanG : Submodule.span ℝ G ≤
            Submodule.span ℝ ({y} : Set E) ⊔ Submodule.span ℝ (H ∩ G) := by
          apply Submodule.span_le.mpr
          apply (hK.trans hpair.2.1).subset_of_vertices hmed (Submodule.convex _)
          intro z hz
          by_cases hzH : z ∈ H
          · exact Submodule.mem_sup_right (Submodule.subset_span ⟨hzH,hz.2⟩)
          by_cases hzy : z = y
          · subst z
            exact Submodule.mem_sup_left (Submodule.subset_span (mem_singleton y))
          have hzK := hK.extreme_mem hz.1 (hpair.2.1.subset hz.2)
          obtain ⟨u,hu,v,hv,he⟩ := hH.exchange hmed hK hHH (hFn.mono hFH)
            hyK ((hHH.not_mem_iff hyK).mp hyH) hzK ((hHH.not_mem_iff hzK).mp hzH)
          have huK := hK.extreme_mem hu.2 (hH.1.subset hu.1)
          have hvK := hK.extreme_mem hv.2 (hH.1.subset hv.1)
          have huG : u ∈ G := by
            rcases hpair.vertex_mem huK with huF | huG
            · have hvF : v ∈ F := by
                rcases hpair.vertex_mem hvK with hvF | hvG
                · exact hvF
                · have huG := (face_mem_of_parallelogram hpair.2.1 hz.2 hvG
                    hyK.1 huK.1 he.symm).2
                  exact False.elim (disjoint_left.mp hpair.2.2.1 huF huG)
              have huv := hn u ⟨huF,hu.2⟩ v ⟨hvF,hv.2⟩
                y ⟨hyG,hy⟩ z ⟨hz.2,hz.1⟩ (by simpa [add_comm] using he)
              have hyz : y = z := by simpa [huv] using he
              exact False.elim (hzy hyz.symm)
            · exact huG
          have hvG : v ∈ G :=
            (face_mem_of_parallelogram hpair.2.1 hyG huG hzK.1 hvK.1 he).2
          have hzEq : z = y+u-v := by rw [he]; abel
          rw [hzEq]
          exact (Submodule.span ℝ ({y}:Set E) ⊔ Submodule.span ℝ (H ∩ G)).sub_mem
            ((Submodule.span ℝ ({y}:Set E) ⊔ Submodule.span ℝ (H ∩ G)).add_mem
              (Submodule.mem_sup_left (Submodule.subset_span (mem_singleton y)))
              (Submodule.mem_sup_right (Submodule.subset_span ⟨hu.1,huG⟩)))
            (Submodule.mem_sup_right (Submodule.subset_span ⟨hv.1,hvG⟩))
        exact (disjoint_span_insert _ _ (Submodule.span ℝ H) hdis
          (Submodule.span_mono hFH) (Submodule.span_mono inter_subset_left)
          (vertex_not_mem_span_face hmed hK hp hH.1 hyK hyH)).mono_right hspanG
      · simp [not_nonempty_iff_eq_empty.mp hGn]
    · simp [not_nonempty_iff_eq_empty.mp hFn]

theorem nonsplit_vertex_parallelogram (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hpair : IsParallelPair K F G) (hns : ¬ IsSplitFace K F) :
    ∃ x ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ z ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ y ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ,
      ∃ w ∈ G ∩ (closedBall (0:E) 1).extremePoints ℝ, x ≠ z ∧ x+y=z+w := by
  classical
  by_contra! hn
  apply hns
  refine ⟨G,hpair,split_of_no_vertex_parallelogram hmed hK hp hpair ?_⟩
  intro x hx z hz y hy w hw he
  by_contra hne
  exact hn x hx z hz y hy w hw hne he

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Splitting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Metric

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst520 : FiniteDimensional ℝ E] [inst521 : Nontrivial E]

lemma maximal_unit_face_vertex_sign (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    {x : E} (hx : x ∈ (closedBall (0:E) 1).extremePoints ℝ) : x ∈ K ∨ -x ∈ K := by
  obtain ⟨f,hf,he⟩ := maximal_unit_face_support hmed hK hn
  rcases extreme_dual_eval_eq_one_or_neg_one hmed hx hf with h | h
  · exact Or.inl (he.symm ▸ ⟨hx.1,h⟩)
  · exact Or.inr (he.symm ▸ ⟨(extreme_unit_neg hx).1,by simp [h]⟩)

omit inst520 inst521 in
lemma supporting_sum_eval [FiniteDimensional ℝ E] [Nontrivial E] {a b h t : E →L[ℝ] ℝ}
    (hh : h ∈ closedBall (0 : E →L[ℝ] ℝ) 1)
    (ht : t ∈ closedBall (0 : E →L[ℝ] ℝ) 1) (he : a+b=h+t)
    {x : E} (hx : x ∈ closedBall (0:E) 1) {s : ℝ} (hs : s=1 ∨ s= -1)
    (ha : a x=s) (hb : b x=s) : h x=s := by
  have h1 := dual_eval_bounds (mem_closedBall_zero_iff.mp hh) hx
  have h2 := dual_eval_bounds (mem_closedBall_zero_iff.mp ht) hx
  have h3 := congrArg (fun f : E →L[ℝ] ℝ => f x) he
  change a x+b x=h x+t x at h3
  rcases hs with rfl | rfl <;> linarith

lemma crossing_support (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hKn : K.Nonempty)
    {f1 f2 f3 f4 : E →L[ℝ] ℝ}
    (hf1 : f1 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hf2 : f2 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hf3 : f3 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hf4 : f4 ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hneg : ∀ x ∈ K, ¬ (f1 x= -1 ∧ f2 x= -1))
    (hpos : ∀ x ∈ K, ¬ (f3 x=1 ∧ f4 x=1)) :
    ∃ h ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ,
      (∀ x ∈ closedBall (0:E) 1, f1 x=1 → f3 x=1 → h x= -1) ∧
      (∀ x ∈ closedBall (0:E) 1, f1 x= -1 → f3 x= -1 → h x=1) ∧
      (∀ x ∈ closedBall (0:E) 1, f2 x=1 → f4 x=1 → h x=1) ∧
      (∀ x ∈ closedBall (0:E) 1, f2 x= -1 → f4 x= -1 → h x= -1) := by
  let B := closedBall (0 : E →L[ℝ] ℝ) 1
  let A := faceHull B ({-f1} ∪ {-f3})
  let C := faceHull B ({f2} ∪ {f4})
  have hA : IsFace B A := isFace_faceHull (convex_closedBall _ _)
    (union_subset (singleton_subset_iff.mpr (extreme_unit_neg hf1).1)
      (singleton_subset_iff.mpr (extreme_unit_neg hf3).1))
  have hC : IsFace B C := isFace_faceHull (convex_closedBall _ _)
    (union_subset (singleton_subset_iff.mpr hf2.1) (singleton_subset_iff.mpr hf4.1))
  have h1 : -f1 ∈ A := subset_faceHull (Or.inl (mem_singleton _))
  have h3 : -f3 ∈ A := subset_faceHull (Or.inr (mem_singleton _))
  have h2 : f2 ∈ C := subset_faceHull (Or.inl (mem_singleton _))
  have h4 : f4 ∈ C := subset_faceHull (Or.inr (mem_singleton _))
  have hn : (A ∩ C).Nonempty := by
    by_contra hn
    have hd : Disjoint A C := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨x,hx,hxA,hxC⟩ := dual_disjoint_faces_primal_vertex hdual hA hC ⟨_,h1⟩ ⟨_,h2⟩ hd
    have hx1 : f1 x= -1 := by have := hxA _ h1; change -f1 x=1 at this; linarith
    have hx3 : f3 x= -1 := by have := hxA _ h3; change -f3 x=1 at this; linarith
    have hx2 := hxC _ h2
    have hx4 := hxC _ h4
    rcases maximal_unit_face_vertex_sign hmed hK hKn hx with hxK | hxK
    · exact hneg x hxK ⟨hx1,hx2⟩
    · exact hpos (-x) hxK ⟨by simp [hx3],by simp [hx4]⟩
  obtain ⟨h,hh,hhA,hhC⟩ := (hA.inter hC).exists_vertex hdual hn
  obtain ⟨t,ht,het⟩ := vertex_in_two_vertex_face hdual (extreme_unit_neg hf1)
    (extreme_unit_neg hf3) hh hhA
  obtain ⟨u,hu,heu⟩ := vertex_in_two_vertex_face hdual hf2 hf4 hh hhC
  refine ⟨h,hh,?_,?_,?_,?_⟩
  · intro x hx h1 h3
    exact supporting_sum_eval hh.1 ht.1 het hx (Or.inr rfl) (by simp [h1]) (by simp [h3])
  · intro x hx h1 h3
    exact supporting_sum_eval hh.1 ht.1 het hx (Or.inl rfl) (by simp [h1]) (by simp [h3])
  · intro x hx h2 h4
    exact supporting_sum_eval hh.1 hu.1 heu hx (Or.inl rfl) h2 h4
  · intro x hx h2 h4
    exact supporting_sum_eval hh.1 hu.1 heu hx (Or.inr rfl) h2 h4

theorem mface_split_core (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {K F F' N1 N1' N2 N2' : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (pF : IsParallelPair K F F') (hmF : HasMFaceStructure F)
    (hmax : HasMaximalMRank F)
    (p1 : IsParallelPair K N1 N1') (p2 : IsParallelPair K N2 N2')
    (hF1 : IsMaximalProperFace F (F ∩ N1))
    (_ : IsMaximalProperFace F (F ∩ N2))
    (hmeet : (F ∩ N1 ∩ N2).Nonempty) (hdis : Disjoint N1' N2')
    {x1 x2 y1 y2 : E}
    (hx1 : x1 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx2 : x2 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy1 : y1 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy2 : y2 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx1n : x1 ∈ N1' ∩ N2) (hx2n : x2 ∈ N1 ∩ N2')
    (he : x1+y1=x2+y2) : False := by
  have hFb := hK.1.trans pF.1
  have hFp := proper_unit_face_subface_ne hK.1 hK.2.1 pF.1.subset
  have hx1K := hK.1.extreme_mem hx1.2 (pF.1.subset hx1.1)
  have hx2K := hK.1.extreme_mem hx2.2 (pF.1.subset hx2.1)
  have hy1K := hK.1.extreme_mem hy1.2 (pF.2.1.subset hy1.1)
  have hy2K := hK.1.extreme_mem hy2.2 (pF.2.1.subset hy2.1)
  obtain ⟨G,H,hG,hH,hGn,hHn,hGH,hx1H,hx2H⟩ :
      ∃ G H, IsMaximalProperFace F G ∧ IsMaximalProperFace F H ∧
        G.Nonempty ∧ H.Nonempty ∧ Disjoint G H ∧ x1 ∈ H ∧ x2 ∈ H := by
    obtain ⟨G,H,hG,hH,hGn,hHn,hGH⟩ := hmF
    have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
    obtain ⟨G',pG⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
      hG hH hGn hHn hGH).1
    have hy1G' := (pG.not_mem_iff hy1K).mp
      (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy1.1)
    have hy2G' := (pG.not_mem_iff hy2K).mp
      (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy2.1)
    have hh : x1 ∈ G ↔ x2 ∈ G := by
      constructor
      · intro hx
        by_contra hn
        have hx2G' := (pG.not_mem_iff hx2K).mp hn
        exact disjoint_left.mp pG.2.2.1 hx
          (face_mem_of_parallelogram pG.2.1 hx2G' hy2G' hx1K.1 hy1K.1 he.symm).1
      · intro hx
        by_contra hn
        have hx1G' := (pG.not_mem_iff hx1K).mp hn
        exact disjoint_left.mp pG.2.2.1 hx
          (face_mem_of_parallelogram pG.2.1 hx1G' hy1G' hx2K.1 hy2K.1 he).1
    rcases pGH.vertex_mem (hFb.extreme_mem hx1.2 hx1.1) with hx | hx
    · exact ⟨H,G,hH,hG,hHn,hGn,hGH.symm,hx,hh.mp hx⟩
    · exact ⟨G,H,hG,hH,hGn,hHn,hGH,hx,
        (pGH.not_mem_iff (hFb.extreme_mem hx2.2 hx2.1)).mp
          (fun hg => disjoint_left.mp hGH (hh.mpr hg) hx)⟩
  have pGH := maximal_pair_of_disjoint hmed hFb hG hH hGn hHn hGH
  obtain ⟨G',pG⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
    hG hH hGn hHn hGH).1
  obtain ⟨H',pH⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
    hG hH hGn hHn hGH).2
  have hx1G' := (pG.not_mem_iff hx1K).mp (fun hh => disjoint_left.mp hGH hh hx1H)
  have hx2G' := (pG.not_mem_iff hx2K).mp (fun hh => disjoint_left.mp hGH hh hx2H)
  have hy1G' := (pG.not_mem_iff hy1K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy1.1)
  have hy2G' := (pG.not_mem_iff hy2K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hG.1.subset hh) hy2.1)
  have hy1H' := (pH.not_mem_iff hy1K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hH.1.subset hh) hy1.1)
  have hy2H' := (pH.not_mem_iff hy2K).mp
    (fun hh => disjoint_left.mp pF.2.2.1 (hH.1.subset hh) hy2.1)
  have hyNs := p1.symm.square hx1n.1 hx2n.1 hy1K hy2K he
  have hyMs := p2.square hx1n.2 hx2n.2 hy1K hy2K he
  obtain ⟨f1,hf1,eN1,eN1'⟩ := p1.support_dual_vertex hmed hK.1 ⟨_,hx2n.1⟩ ⟨_,hx1n.1⟩
  obtain ⟨f2,hf2,eN2,eN2'⟩ := p2.support_dual_vertex hmed hK.1 ⟨_,hx1n.2⟩ ⟨_,hx2n.2⟩
  obtain ⟨f3,hf3,eG,eG'⟩ := pG.support_dual_vertex hmed hK.1 hGn ⟨_,hx1G'⟩
  obtain ⟨f4,hf4,eH,eH'⟩ := pH.support_dual_vertex hmed hK.1 hHn ⟨_,hy1H'⟩
  obtain ⟨h,hh,h13,h13',h24,h24'⟩ := crossing_support hmed hdual hK
    ⟨_,hx1K.1⟩ hf1 hf2 hf3 hf4
    (fun x hx he => disjoint_left.mp hdis (by rw [eN1']; exact ⟨hx,he.1⟩)
      (by rw [eN2']; exact ⟨hx,he.2⟩))
    (fun x hx he => disjoint_left.mp hGH (by rw [eG]; exact ⟨hx,he.1⟩)
      (by rw [eH]; exact ⟨hx,he.2⟩))
  let T := {x ∈ K | h x=1}
  let T' := {x ∈ K | h x= -1}
  have pT : IsParallelPair K T T' := parallelPair_of_dual_vertex hmed hK.1 hh
  have hNG : N1 ∩ G ⊆ T' := fun x hx =>
    ⟨p1.1.subset hx.1,h13 x (hK.1.subset (p1.1.subset hx.1))
      (eN1 ▸ hx.1).2 (eG ▸ hx.2).2⟩
  have hNG' : N1' ∩ G' ⊆ T := fun x hx =>
    ⟨p1.2.1.subset hx.1,h13' x (hK.1.subset (p1.2.1.subset hx.1))
      (eN1' ▸ hx.1).2 (eG' ▸ hx.2).2⟩
  have hNH : N2 ∩ H ⊆ T := fun x hx =>
    ⟨p2.1.subset hx.1,h24 x (hK.1.subset (p2.1.subset hx.1))
      (eN2 ▸ hx.1).2 (eH ▸ hx.2).2⟩
  have hNH' : N2' ∩ H' ⊆ T' := fun x hx =>
    ⟨p2.2.1.subset hx.1,h24' x (hK.1.subset (p2.2.1.subset hx.1))
      (eN2' ▸ hx.1).2 (eH' ▸ hx.2).2⟩
  have hx1T := hNH ⟨hx1n.2,hx1H⟩
  have hy2T := hNG' ⟨hyNs.2,hy2G'⟩
  have hy1T' := hNH' ⟨hyMs.1,hy1H'⟩
  have hx2T' := (pT.square hy2T hy1T' hx2K hx1K
    (by simpa [add_comm] using he.symm)).1
  have hHmeet : (H ∩ N1 ∩ N2).Nonempty := by
    by_contra hn
    obtain ⟨w,hw,⟨hwF,hwN1⟩,hwN2⟩ := ((hFb.inter (hK.1.trans p1.1)).inter
      (hK.1.trans p2.1)).exists_vertex hmed hmeet
    have hwH : w ∉ H := fun hh => hn ⟨w,⟨hh,hwN1⟩,hwN2⟩
    have hwG := (pGH.symm.not_mem_iff (hFb.extreme_mem hw hwF)).mp hwH
    have hGn1 : (G ∩ N1').Nonempty := by
      by_contra hn1
      have hsub : G ⊆ F ∩ N1 := fun x hx => ⟨hG.1.subset hx,
        p1.symm.subset_of_disjoint hmed hK.1 (pF.1.trans hG.1)
          (disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn1)) hx⟩
      have heG := hG.2.2 _ hF1.1 hsub hF1.2.1
      exact disjoint_left.mp hGH (heG ▸ ⟨hx2.1,hx2n.1⟩) hx2H
    obtain ⟨v,hv,hvG,hvN1'⟩ := ((hFb.trans hG.1).inter
      (hK.1.trans p1.2.1)).exists_vertex hmed hGn1
    have hvN2 := (p2.symm.not_mem_iff (hK.1.extreme_mem hv (pG.1.subset hvG))).mp
      (fun hh => disjoint_left.mp hdis hvN1' hh)
    obtain ⟨a,ha,b,hb,hab⟩ := hH.exchange hmed hFb pGH.symm hHn
      (hFb.extreme_mem hv (hG.1.subset hvG)) hvG
      (hFb.extreme_mem hw hwF) hwG
    have hs := p1.symm.square hvN1' hwN1
      (hK.1.extreme_mem ha.2 (pH.1.subset ha.1))
      (hK.1.extreme_mem hb.2 (pH.1.subset hb.1)) hab
    have hbN2 : b ∈ N2 := (p2.symm.not_mem_iff
      (hK.1.extreme_mem hb.2 (pH.1.subset hb.1))).mp
        (fun hh => disjoint_left.mp hdis hs.2 hh)
    have haN2 := (face_mem_of_parallelogram p2.1 hwN2 hbN2
      (pG.1.subset hvG) (pH.1.subset ha.1) hab.symm).2
    exact hn ⟨a,⟨ha.1,hs.1⟩,haN2⟩
  obtain ⟨y,hy,⟨hyH,hyN1⟩,hyN2⟩ := (((hFb.trans hH.1).inter
    (hK.1.trans p1.1)).inter (hK.1.trans p2.1)).exists_vertex hmed hHmeet
  have hyT := hNH ⟨hyN2,hyH⟩
  obtain ⟨d,hd,c,hc,hec⟩ := hG.exchange hmed hFb pGH hGn
    (hFb.extreme_mem hx2.2 hx2.1) hx2H
    (hFb.extreme_mem hy (hH.1.subset hyH)) hyH
  have hs := p2.symm.square hx2n.2 hyN2
    (hK.1.extreme_mem hd.2 (pG.1.subset hd.1))
    (hK.1.extreme_mem hc.2 (pG.1.subset hc.1)) hec
  have hcN1 : c ∈ N1 := (p1.symm.not_mem_iff
    (hK.1.extreme_mem hc.2 (pG.1.subset hc.1))).mp
      (fun hh => disjoint_left.mp hdis hh hs.2)
  have hdN1 := (face_mem_of_parallelogram p1.1 hyN1 hcN1
    hx2K.1 (pG.1.subset hd.1) hec.symm).2
  have hdT' := hNG ⟨hdN1,hd.1⟩
  have hyT' := (face_mem_of_parallelogram pT.2.1 hx2T' hdT'
    (hH.1.subset.trans pF.1.subset hyH) (pG.1.subset hc.1) hec).1
  exact disjoint_left.mp pT.2.2.1 hyT hyT'

end

section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

namespace ZeroSumFour
variable {E}

lemma sum_entry (x : ZeroSumFour E) : ∑ i, entry x i = 0 := by
  have hx := x.property
  change (fourSum E) x.val = 0 at hx
  rw [fourSum, LinearMap.sum_apply] at hx
  exact hx

lemma norm_eq_sum (x : ZeroSumFour E) : ‖x‖ = ∑ i, ‖entry x i‖ :=
  PiLp.norm_eq_of_L1 x.val

lemma pair_norm_add (x : ZeroSumFour E) (i j : Fin 4) (hij : i ≠ j) (m : E)
    (hi : ‖m‖+‖entry x i-m‖ = ‖entry x i‖)
    (hj : ‖m‖+‖entry x j+m‖ = ‖entry x j‖) :
    ‖pair i j m‖+‖x-pair i j m‖ = ‖x‖ := by
  rw [norm_eq_sum, norm_eq_sum, norm_eq_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hki : k = i
  · subst k
    simpa [hij] using hi
  by_cases hkj : k = j
  · subst k
    simpa [hij,Ne.symm hij,sub_neg_eq_add] using hj
  simp [hki,hkj]

lemma pair_additive_of_extreme (hmed : HasMetricMedians E)
    {x : ZeroSumFour E}
    (hx : x ∈ (closedBall (0 : ZeroSumFour E) 1).extremePoints ℝ)
    (hnx : ‖x‖ = 1) (i j : Fin 4) (hij : i ≠ j)
    (hout : ∃ k, k ≠ i ∧ k ≠ j ∧ entry x k ≠ 0) :
    ‖entry x i + entry x j‖ = ‖entry x i‖ + ‖entry x j‖ := by
  obtain ⟨m,hm⟩ := hmed ![0,entry x i,-entry x j]
  have hi : ‖m‖+‖entry x i-m‖ = ‖entry x i‖ := by
    have ht := hm 0 1 (by decide)
    simpa [dist_eq_norm,norm_sub_rev] using ht.symm
  have hj : ‖m‖+‖entry x j+m‖ = ‖entry x j‖ := by
    have ht := hm 0 2 (by decide)
    simpa [dist_eq_norm,neg_sub,norm_sub_rev,add_comm] using ht.symm
  have he := extreme_unit_norm_add hx hnx ((pair_norm_add x i j hij m hi hj).trans hnx)
  obtain ⟨k,hki,hkj,hk⟩ := hout
  have hnc : ‖pair i j m‖ = 0 := by
    have ht := congrArg (fun v : ZeroSumFour E => entry v k) he
    have he' : (0:E) = ‖pair i j m‖ • entry x k := by simpa [hki,hkj] using ht
    exact (smul_eq_zero.mp he'.symm).resolve_right hk
  have hp0 : pair i j m = 0 := norm_eq_zero.mp hnc
  have hm0 : m = 0 := by
    have ht := congrArg (fun v : ZeroSumFour E => entry v i) hp0
    simpa [hij] using ht
  have ht := hm 1 2 (by decide)
  simpa [dist_eq_norm,sub_neg_eq_add,hm0] using ht

theorem extreme_four_norms (hmed : HasMetricMedians E)
    {x : ZeroSumFour E}
    (hx : x ∈ (closedBall (0 : ZeroSumFour E) 1).extremePoints ℝ)
    (hnx : ‖x‖ = 1)
    (hout : ∀ i j : Fin 4, i ≠ j → ∃ k, k ≠ i ∧ k ≠ j ∧ entry x k ≠ 0) :
    (∀ i, ‖entry x i‖ = 1/4) ∧
      ∀ i j, i ≠ j → ‖entry x i+entry x j‖ = 1/2 := by
  have ha (i j : Fin 4) (hij : i ≠ j) :=
    pair_additive_of_extreme hmed hx hnx i j hij (hout i j hij)
  have hs := sum_entry x
  simp only [Fin.sum_univ_four] at hs
  have h01 : -(entry x 0+entry x 1) = entry x 2+entry x 3 := by
    apply neg_eq_iff_add_eq_zero.mpr
    convert hs using 1 ; abel
  have h02 : -(entry x 0+entry x 2) = entry x 1+entry x 3 := by
    apply neg_eq_iff_add_eq_zero.mpr
    convert hs using 1 ; abel
  have h03 : -(entry x 0+entry x 3) = entry x 1+entry x 2 := by
    apply neg_eq_iff_add_eq_zero.mpr
    convert hs using 1 ; abel
  have hc01 := congrArg norm h01
  have hc02 := congrArg norm h02
  have hc03 := congrArg norm h03
  simp only [norm_neg, ha 0 1 (by decide),ha 2 3 (by decide)] at hc01
  simp only [norm_neg, ha 0 2 (by decide),ha 1 3 (by decide)] at hc02
  simp only [norm_neg, ha 0 3 (by decide),ha 1 2 (by decide)] at hc03
  have hsum := (norm_eq_sum x).symm.trans hnx
  simp only [Fin.sum_univ_four] at hsum
  have hn0 : ‖entry x 0‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn1 : ‖entry x 1‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn2 : ‖entry x 2‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn3 : ‖entry x 3‖ = 1/4 := by linarith only [hc01,hc02,hc03,hsum]
  have hn (i : Fin 4) : ‖entry x i‖ = 1/4 := by
    fin_cases i
    · exact hn0
    · exact hn1
    · exact hn2
    · exact hn3
  exact ⟨hn,fun i j hij => by rw [ha i j hij,hn i,hn j]; norm_num⟩
end ZeroSumFour

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst526 : FiniteDimensional ℝ E]

omit inst526 in
lemma IsCompact.exists_extreme_ge [FiniteDimensional ℝ E] {K : Set E} (hc : IsCompact K)
    (f : E →L[ℝ] ℝ) {x : E} (hx : x ∈ K) :
    ∃ y ∈ K.extremePoints ℝ, f x ≤ f y := by
  let S := {y ∈ K | ∀ z ∈ K, f z ≤ f y}
  have hS : IsExposed ℝ K S := fun _ => ⟨f,rfl⟩
  obtain ⟨z,hzK,hz⟩ := hc.exists_isMaxOn ⟨x,hx⟩ f.continuous.continuousOn
  obtain ⟨y,hy⟩ := (hS.isCompact hc).extremePoints_nonempty ⟨z,hzK,hz⟩
  exact ⟨y,hS.isExtreme.extremePoints_subset_extremePoints hy,hy.1.2 x hx⟩

omit inst526 in
lemma normalized_mem_exposed [FiniteDimensional ℝ E] {f : E →L[ℝ] ℝ} {F : Set E}
    (hF : F = {x ∈ closedBall (0:E) 1 | f x = 1}) {x : E}
    (hx : x ≠ 0) (he : f x = ‖x‖) : ‖x‖⁻¹ • x ∈ F := by
  rw [hF]
  have hn := norm_pos_iff.mpr hx
  constructor
  · apply mem_closedBall_zero_iff.mpr
    simp [norm_smul,ne_of_gt hn]
  · simp [he,ne_of_gt hn]

namespace ZeroSumFour

lemma coordinate_extreme {f : Fin 4 → E →L[ℝ] ℝ}
    (hf : ∀ i, ‖f i‖ ≤ 1) {q : ZeroSumFour E}
    (hq : ‖q‖ ≤ 1) (he : ∀ i, f i (entry q i) = ‖entry q i‖)
    (hn : ‖q‖ = 1) :
    ∃ r ∈ (closedBall (0 : ZeroSumFour E) 1).extremePoints ℝ,
      ‖r‖ = 1 ∧ (∀ i, f i (entry r i) = ‖entry r i‖) ∧
      f 2 (entry q 2) ≤ f 2 (entry r 2) := by
  let L : ZeroSumFour E →L[ℝ] ℝ := ∑ i, (f i).comp (entryL i)
  have hLi (x : ZeroSumFour E) (i : Fin 4) : f i (entry x i) ≤ ‖entry x i‖ :=
    (le_abs_self _).trans ((f i).le_opNorm _ |>.trans
      (mul_le_of_le_one_left (norm_nonneg _) (hf i)))
  have hLe (x : ZeroSumFour E) : L x = ∑ i, f i (entry x i) := by simp [L]
  have hLb : ∀ x ∈ closedBall (0 : ZeroSumFour E) 1, L x ≤ 1 := by
    intro x hx
    rw [hLe]
    exact (Finset.sum_le_sum (fun i _ => hLi x i)).trans
      ((norm_eq_sum x).symm.le.trans (mem_closedBall_zero_iff.mp hx))
  let S := {x ∈ closedBall (0 : ZeroSumFour E) 1 | L x = 1}
  have hS := IsFace.of_support_le (convex_closedBall (0 : ZeroSumFour E) 1) L.toLinearMap 1 hLb
  have hSc : IsCompact S := (isCompact_closedBall (0 : ZeroSumFour E) 1).inter_right
    (isClosed_eq L.continuous continuous_const)
  have hqS : q ∈ S := ⟨mem_closedBall_zero_iff.mpr hq,by
    rw [hLe]
    simp_rw [he]
    rw [← norm_eq_sum,hn]⟩
  obtain ⟨r,hr,hqr⟩ := IsCompact.exists_extreme_ge hSc ((f 2).comp (entryL 2)) hqS
  have hrB := hS.2.extremePoints_subset_extremePoints hr
  have hrr : ‖r‖ = 1 := le_antisymm (mem_closedBall_zero_iff.mp hrB.1) (by
    rw [norm_eq_sum,← hr.1.2,hLe]
    exact Finset.sum_le_sum (fun i _ => hLi r i))
  refine ⟨r,hrB,hrr,?_,hqr⟩
  intro i
  have hs : ∑ i, f i (entry r i) = ∑ i, ‖entry r i‖ := by
    rw [← hLe,hr.1.2,← norm_eq_sum,hrr]
  exact (Finset.sum_eq_sum_iff_of_le (fun i _ => hLi r i)).mp hs i (Finset.mem_univ i)
end ZeroSumFour

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst529 : FiniteDimensional ℝ E] [inst530 : Nontrivial E]

omit inst529 inst530 in
lemma faceHull_union_generators [FiniteDimensional ℝ E] [Nontrivial E] {F C : Set E} {a c : E}
    (ha : faceHull (closedBall (0:E) 1) {a} = F)
    (hc : faceHull (closedBall (0:E) 1) {c} = C)
    (haB : a ∈ closedBall (0:E) 1) (hcB : c ∈ closedBall (0:E) 1) :
    faceHull (closedBall (0:E) 1) ({a} ∪ {c}) =
      faceHull (closedBall (0:E) 1) (F ∪ C) := by
  have haF : a ∈ F := ha ▸ subset_faceHull (mem_singleton _)
  have hcC : c ∈ C := hc ▸ subset_faceHull (mem_singleton _)
  apply subset_antisymm (faceHull_mono (union_subset_union
    (singleton_subset_iff.mpr haF) (singleton_subset_iff.mpr hcC)))
  apply faceHull_min (isFace_faceHull (convex_closedBall _ _)
    (union_subset (singleton_subset_iff.mpr haB) (singleton_subset_iff.mpr hcB)))
  rw [← ha,← hc]
  exact union_subset (faceHull_mono subset_union_left) (faceHull_mono subset_union_right)

theorem two_face_exchange (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) {K F C : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hF : IsFace K F) (hC : IsFace K C) (hFn : F.Nonempty) (hCn : C.Nonempty)
    {y : E} (hy : y ∈ (closedBall (0:E) 1).extremePoints ℝ)
    (hyJ : y ∈ faceHull (closedBall (0:E) 1) (F ∪ C))
    (hyF : y ∉ F) (hyC : y ∉ C) :
    ∃ a ∈ F, ∃ c ∈ C, ∃ z ∈ K, a+c=y+z := by
  classical
  have hFb := hK.trans hF
  have hCb := hK.trans hC
  obtain ⟨a,ha,haG⟩ := hFb.exists_generator hmed hFn
  obtain ⟨c,hc,hcG⟩ := hCb.exists_generator hmed hCn
  let w := (1/2:ℝ) • a+(1/2:ℝ) • c
  have hwK : w ∈ K := hK.1 (hF.subset ha) (hC.subset hc)
    (by norm_num) (by norm_num) (by norm_num)
  have hwG : faceHull (closedBall (0:E) 1) {w} =
      faceHull (closedBall (0:E) 1) (F ∪ C) :=
    (faceHull_midpoint_eq (convex_closedBall _ _) (hFb.subset ha) (hCb.subset hc)).trans
      (faceHull_union_generators haG hcG (hFb.subset ha) (hCb.subset hc))
  have hyK := faceHull_min hK (union_subset hF.subset hC.subset) hyJ
  obtain ⟨t,ht,ht1,z,hzB,hw⟩ := faceHull_radial hdual (hK.subset hwK) (hwG.symm ▸ hyJ)
  have hzK : z ∈ K := hK.2.right_mem_of_mem_openSegment hy.1 hzB hwK
    ⟨t,1-t,ht,sub_pos.mpr ht1,by ring,hw.symm⟩
  have hnorm (x : E) (hx : x ∈ K) : ‖x‖ = 1 := norm_eq_one_of_mem_proper_face hK.2 hp hx
  obtain ⟨f,hfn,hf⟩ := hFb.exposed_generator hmed hFn
    (proper_unit_face_subface_ne hK hp hF.subset)
  obtain ⟨g,hgn,hg⟩ := hCb.exposed_generator hmed hCn
    (proper_unit_face_subface_ne hK hp hC.subset)
  have hY : IsFace (closedBall (0:E) 1) {y} := ⟨convex_singleton y,isExtreme_singleton.mpr hy⟩
  obtain ⟨s,hsn,hs⟩ := hY.exposed_generator hmed (singleton_nonempty y)
    (proper_unit_face_subface_ne hK hp (singleton_subset_iff.mpr hyK))
  obtain ⟨k,hkv,hk⟩ := proper_face_support hmed hK ⟨y,hyK⟩ hp
  have hkn := mem_closedBall_zero_iff.mp hkv.1
  have hfa := (hf ▸ ha).2
  have hgc := (hg ▸ hc).2
  have hsy := (hs ▸ mem_singleton y).2
  have heq : (1/4:ℝ) • a+(1/4:ℝ) • c+(-(t/2)) • y+(-((1-t)/2)) • z = 0 := by
    calc
      _ = (1/2:ℝ) • (w - (t • y+(1-t) • z)) := by dsimp [w]; module
      _ = 0 := by rw [hw,sub_self,smul_zero]
  let q := ZeroSumFour.ofFour ((1/4:ℝ) • a) ((1/4:ℝ) • c)
    ((-(t/2)) • y) ((-((1-t)/2)) • z) heq
  let fs : Fin 4 → E →L[ℝ] ℝ := ![f,g,-s,-k]
  have hfs : ∀ i, ‖fs i‖ ≤ 1 := by
    intro i
    fin_cases i <;> simp [fs,hfn,hgn,hsn,hkn]
  have hqn : ‖q‖ = 1 := by
    rw [ZeroSumFour.norm_eq_sum]
    simp only [Fin.sum_univ_four]
    simp [q,ZeroSumFour.entry_ofFour,norm_smul,hnorm a (hF.subset ha),
      hnorm c (hC.subset hc),hnorm y hyK,hnorm z hzK,
      abs_of_nonneg ht.le,abs_of_nonneg (sub_nonneg.mpr ht1.le)]
    ring
  have hqe : ∀ i, fs i (ZeroSumFour.entry q i) = ‖ZeroSumFour.entry q i‖ := by
    intro i
    fin_cases i <;> simp [fs,q,ZeroSumFour.entry_ofFour,norm_smul,hfa,hgc,hsy,hk z hzK,
      hnorm a (hF.subset ha),hnorm c (hC.subset hc),hnorm y hyK,hnorm z hzK,
      abs_of_nonneg ht.le,abs_of_nonneg (sub_nonneg.mpr ht1.le)]
  obtain ⟨r,hr,hrn,hre,hqr⟩ := ZeroSumFour.coordinate_extreme hfs hqn.le hqe hqn
  let v := ZeroSumFour.entry r
  have hv0 : f (v 0) = ‖v 0‖ := hre 0
  have hv1 : g (v 1) = ‖v 1‖ := hre 1
  have hv2 : s (-v 2) = ‖v 2‖ := by simpa [fs,v] using hre 2
  have hv3 : k (-v 3) = ‖v 3‖ := by simpa [fs,v] using hre 3
  have hv2pos : 0 < ‖v 2‖ := by
    have hq2 : fs 2 (ZeroSumFour.entry q 2) = t/2 := by simp [fs,q,hsy]
    rw [hq2,hre 2] at hqr
    dsimp [v]
    linarith
  have hv2ne : -v 2 ≠ 0 := neg_ne_zero.mpr (norm_pos_iff.mp hv2pos)
  have hv2y : ‖v 2‖⁻¹ • (-v 2) = y := by
    have hh := normalized_mem_exposed hs hv2ne (by simpa using hv2)
    simpa using hh
  have hv2e : -v 2 = ‖v 2‖ • y := by
    rw [← hv2y,smul_smul,mul_inv_cancel₀ (ne_of_gt hv2pos),one_smul]
  have hvs : v 0+v 1 = -v 2 + -v 3 := by
    have hh := ZeroSumFour.sum_entry r
    simp only [Fin.sum_univ_four] at hh
    change v 0+v 1+v 2+v 3=0 at hh
    calc
      _ = (v 0+v 1+v 2+v 3)-v 2-v 3 := by abel
      _ = _ := by rw [hh]; abel
  have hkv0 : k (v 0) = ‖v 0‖ := by
    by_cases hh : v 0 = 0
    · simp [hh]
    have hn := norm_pos_iff.mpr hh
    have hmem := normalized_mem_exposed hf hh hv0
    have he := hk _ (hF.subset hmem)
    simp only [map_smul,smul_eq_mul] at he
    have hh := congrArg (fun t : ℝ => ‖v 0‖*t) he
    simpa [← mul_assoc,ne_of_gt hn] using hh
  have hkv1 : k (v 1) = ‖v 1‖ := by
    by_cases hh : v 1 = 0
    · simp [hh]
    have hn := norm_pos_iff.mpr hh
    have he := hk _ (hC.subset (normalized_mem_exposed hg hh hv1))
    simp only [map_smul,smul_eq_mul] at he
    have hh := congrArg (fun t : ℝ => ‖v 1‖*t) he
    simpa [← mul_assoc,ne_of_gt hn] using hh
  have hks : ‖v 0‖+‖v 1‖ = ‖v 2‖+‖v 3‖ := by
    have hh := congrArg k hvs
    simpa [hkv0,hkv1,hv3,hv2e,hk y hyK] using hh
  have hv0ne : v 0 ≠ 0 := by
    intro hzero
    have hh := congrArg g hvs
    simp only [map_add,hzero,zero_add,hv1,hv2e,map_smul,smul_eq_mul] at hh
    have hgb : g (-v 3) ≤ ‖v 3‖ := by
      simpa using (le_abs_self (g (-v 3))).trans
        ((g.le_opNorm (-v 3)).trans (mul_le_of_le_one_left (norm_nonneg _) hgn))
    have hgy := (dual_eval_bounds hgn hy.1).2
    have hks' : ‖v 1‖ = ‖v 2‖+‖v 3‖ := by simpa [hzero] using hks
    have hge : g y = 1 := by nlinarith
    exact hyC (hg.symm ▸ ⟨hy.1,hge⟩)
  have hv1ne : v 1 ≠ 0 := by
    intro hzero
    have hh := congrArg f hvs
    simp only [map_add,hzero,add_zero,hv0,hv2e,map_smul,smul_eq_mul] at hh
    have hfb : f (-v 3) ≤ ‖v 3‖ := by
      simpa using (le_abs_self (f (-v 3))).trans
        ((f.le_opNorm (-v 3)).trans (mul_le_of_le_one_left (norm_nonneg _) hfn))
    have hfy := (dual_eval_bounds hfn hy.1).2
    have hks' : ‖v 0‖ = ‖v 2‖+‖v 3‖ := by simpa [hzero] using hks
    have hfe : f y = 1 := by nlinarith
    exact hyF (hf.symm ▸ ⟨hy.1,hfe⟩)
  have hout : ∀ i j : Fin 4, i ≠ j → ∃ l, l ≠ i ∧ l ≠ j ∧ ZeroSumFour.entry r l ≠ 0 := by
    intro i j hij
    by_cases h0 : (0:Fin 4) ≠ i ∧ 0 ≠ j
    · exact ⟨0,h0.1,h0.2,hv0ne⟩
    by_cases h1 : (1:Fin 4) ≠ i ∧ 1 ≠ j
    · exact ⟨1,h1.1,h1.2,hv1ne⟩
    exact ⟨2,by omega,by omega,norm_pos_iff.mp hv2pos⟩
  have hnorms := (ZeroSumFour.extreme_four_norms hmed hr hrn hout).1
  have hn0 : ‖v 0‖ = 1/4 := hnorms 0
  have hn1 : ‖v 1‖ = 1/4 := hnorms 1
  have hn2 : ‖v 2‖ = 1/4 := hnorms 2
  have hn3 : ‖v 3‖ = 1/4 := hnorms 3
  have h0F : (4:ℝ) • v 0 ∈ F := by
    simpa [hn0] using normalized_mem_exposed hf hv0ne hv0
  have h1C : (4:ℝ) • v 1 ∈ C := by
    simpa [hn1] using normalized_mem_exposed hg hv1ne hv1
  have h3B : (4:ℝ) • (-v 3) ∈ closedBall (0:E) 1 := by
    apply mem_closedBall_zero_iff.mpr
    simp [norm_smul,hn3]
  have h2y : (4:ℝ) • (-v 2) = y := by simpa [hn2] using hv2y
  have he : (4:ℝ) • v 0+(4:ℝ) • v 1 = y+(4:ℝ) • (-v 3) := by
    simpa [smul_add,h2y] using congrArg (fun x : E => (4:ℝ) • x) hvs
  have h3K := (face_mem_of_parallelogram hK (hF.subset h0F) (hC.subset h1C) hy.1 h3B he).2
  exact ⟨_,h0F,_,h1C,_,h3K,he⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst533 : FiniteDimensional ℝ E] [inst534 : Nontrivial E]

lemma proper_unit_face_not_neg (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    {x : E} (hx : x ∈ K) : -x ∉ K := by
  obtain ⟨f,hf,hfK⟩ := proper_face_support hmed hK ⟨x,hx⟩ hp
  intro hn
  have h1 := hfK x hx
  have h2 := hfK (-x) hn
  simp only [map_neg] at h2
  linarith

omit inst533 inst534 in
lemma IsParallelPair.restrict_support [FiniteDimensional ℝ E] [Nontrivial E] {K F N : Set E} {f : E →L[ℝ] ℝ}
    (hFK : F ⊆ K) (eN : N = {x ∈ K | f x=1}) :
    F ∩ N = {x ∈ F | f x=1} := by
  rw [eN]
  ext x
  exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hFK h.1,h.2⟩⟩

theorem mface_split_precore (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ))
    {K F F' N1 N1' N2 N2' : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (pF : IsParallelPair K F F') (hmF : HasMFaceStructure F)
    (hmax : HasMaximalMRank F)
    (p1 : IsParallelPair K N1 N1') (p2 : IsParallelPair K N2 N2')
    (hF1 : IsMaximalProperFace F (F ∩ N1))
    (hF2 : IsMaximalProperFace F (F ∩ N2))
    (hmeet : (F ∩ N1 ∩ N2).Nonempty)
    (hdisF : Disjoint (F ∩ N1') (F ∩ N2'))
    {x1 x2 y1 y2 : E}
    (hx1 : x1 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx2 : x2 ∈ F ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy1 : y1 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hy2 : y2 ∈ F' ∩ (closedBall (0:E) 1).extremePoints ℝ)
    (hx1n : x1 ∈ N1' ∩ N2) (hx2n : x2 ∈ N1 ∩ N2')
    (he : x1+y1=x2+y2) : False := by
  by_cases hd : Disjoint N1' N2'
  · exact mface_split_core hmed hdual hK pF hmF hmax p1 p2 hF1 hF2 hmeet hd
      hx1 hx2 hy1 hy2 hx1n hx2n he
  have hFb := hK.1.trans pF.1
  have hFn : F.Nonempty := ⟨_,hx1.1⟩
  let D := N1' ∩ N2'
  let C := N1 ∩ N2 ∩ F'
  let J := faceHull (closedBall (0:E) 1) (F ∪ C)
  have hD : IsFace (closedBall (0:E) 1) D :=
    (hK.1.trans p1.2.1).inter (hK.1.trans p2.2.1)
  have hDn : D.Nonempty := not_disjoint_iff.mp hd
  have hC : IsFace K C := (p1.1.inter p2.1).inter pF.2.1
  have hbase : F ∪ C ⊆ K := union_subset pF.1.subset hC.subset
  have hJ : IsFace (closedBall (0:E) 1) J :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hK.1.subset)
  have hJK : J ⊆ K := faceHull_min hK.1 hbase
  have hFJ : F ⊆ J := fun _ hz => subset_faceHull (Or.inl hz)
  have hCJ : C ⊆ J := fun _ hz => subset_faceHull (Or.inr hz)
  have hJD : Disjoint J D := by
    by_contra hn
    obtain ⟨y,hy,hyJ,hyD⟩ := (hJ.inter hD).exists_vertex hmed (not_disjoint_iff.mp hn)
    have hyF : y ∉ F := fun hh => disjoint_left.mp hdisF ⟨hh,hyD.1⟩ ⟨hh,hyD.2⟩
    have hyC : y ∉ C := fun hh => disjoint_left.mp p1.2.2.1 hh.1.1 hyD.1
    have hCn : C.Nonempty := by
      by_contra hnC
      apply hyF
      apply faceHull_min hFb _ hyJ
      rw [not_nonempty_iff_eq_empty.mp hnC,union_empty]
    obtain ⟨a,ha,c,hc,z,hz,he⟩ := two_face_exchange hmed hdual hK.1 hK.2.1
      pF.1 hC hFn hCn hy hyJ hyF hyC
    have h1 := p1.square_points hmed hK.1 hc.1.1 hyD.1 (pF.1.subset ha) hz
      (by simpa [add_comm] using he)
    have h2 := p2.square_points hmed hK.1 hc.1.2 hyD.2 (pF.1.subset ha) hz
      (by simpa [add_comm] using he)
    exact disjoint_left.mp hdisF ⟨ha,h1.1⟩ ⟨ha,h2.1⟩
  obtain ⟨t,ht,htJ,htD⟩ := disjoint_faces_dual_vertex hmed hJ hD
    (hFn.mono hFJ) hDn hJD
  let L := {x ∈ closedBall (0:E) 1 | t x=1}
  have hL : IsMaximalProperFace (closedBall (0:E) 1) L :=
    dual_vertex_maximal_support hmed ht
  have hFL : F ⊆ L := fun x hx => ⟨hFb.subset hx,htJ x (hFJ hx)⟩
  obtain ⟨A,pA⟩ := maximal_mface_parallel hmed hL.1 hL.2.1
    (hFb.mono hL.1.subset hFL) hmF hmax
  obtain ⟨f1,hf1,eN1,eN1'⟩ := p1.support_dual_vertex hmed hK.1 ⟨_,hx2n.1⟩ ⟨_,hx1n.1⟩
  obtain ⟨f2,hf2,eN2,eN2'⟩ := p2.support_dual_vertex hmed hK.1 ⟨_,hx1n.2⟩ ⟨_,hx2n.2⟩
  let M1 := {x ∈ L | f1 x=1}
  let M1' := {x ∈ L | f1 x= -1}
  let M2 := {x ∈ L | f2 x=1}
  let M2' := {x ∈ L | f2 x= -1}
  have q1 : IsParallelPair L M1 M1' := parallelPair_of_dual_vertex hmed hL.1 hf1
  have q2 : IsParallelPair L M2 M2' := parallelPair_of_dual_vertex hmed hL.1 hf2
  have eF1 : F ∩ M1 = F ∩ N1 := by
    rw [IsParallelPair.restrict_support hFL (show M1={x ∈ L | f1 x=1} from rfl),
      IsParallelPair.restrict_support pF.1.subset eN1]
  have eF2 : F ∩ M2 = F ∩ N2 := by
    rw [IsParallelPair.restrict_support hFL (show M2={x ∈ L | f2 x=1} from rfl),
      IsParallelPair.restrict_support pF.1.subset eN2]
  have hmeetL : (F ∩ M1 ∩ M2).Nonempty := by
    obtain ⟨z,⟨hzF,hzN1⟩,hzN2⟩ := hmeet
    exact ⟨z,⟨hzF,(show z ∈ F ∩ M1 by rw [eF1]; exact ⟨hzF,hzN1⟩).2⟩,(show z ∈ F ∩ M2 by rw [eF2]; exact ⟨hzF,hzN2⟩).2⟩
  have hdisL : Disjoint M1' M2' := by
    by_contra hn
    obtain ⟨z,hz,hz1,hz2⟩ := ((hL.1.trans q1.2.1).inter
      (hL.1.trans q2.2.1)).exists_vertex hmed (not_disjoint_iff.mp hn)
    have hzL : z ∈ L := hz1.1
    rcases maximal_unit_face_vertex_sign hmed hK (hFn.mono pF.1.subset) hz with hzK | hzK
    · have hzD : z ∈ D := ⟨by rw [eN1']; exact ⟨hzK,hz1.2⟩,
          by rw [eN2']; exact ⟨hzK,hz2.2⟩⟩
      have hh := htD z hzD
      linarith [hzL.2]
    · have hzN1 : -z ∈ N1 := by rw [eN1]; exact ⟨hzK,by simp [hz1.2]⟩
      have hzN2 : -z ∈ N2 := by rw [eN2]; exact ⟨hzK,by simp [hz2.2]⟩
      have hzF' : -z ∈ F' := (pF.not_mem_iff
        (hK.1.extreme_mem (extreme_unit_neg hz) hzK)).mp (by
          intro hh
          have hh' := (hFL hh).2
          simp only [map_neg] at hh'
          linarith [hzL.2])
      have hh := htJ (-z) (hCJ ⟨⟨hzN1,hzN2⟩,hzF'⟩)
      simp only [map_neg] at hh
      linarith [hzL.2]
  have htx1 := htJ x1 (hFJ hx1.1)
  have htx2 := htJ x2 (hFJ hx2.1)
  have hty : t y1=t y2 := by
    have hh := congrArg t he
    simp only [map_add,htx1,htx2] at hh
    linarith
  obtain ⟨u1,hu1,u2,hu2,heu⟩ :
      ∃ u1 ∈ A ∩ (closedBall (0:E) 1).extremePoints ℝ,
        ∃ u2 ∈ A ∩ (closedBall (0:E) 1).extremePoints ℝ, x1+u1=x2+u2 := by
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hy1.2 ht with hty1 | hty1
    · have hy1L : y1 ∈ L := ⟨hy1.2.1,hty1⟩
      have hy2L : y2 ∈ L := ⟨hy2.2.1,hty ▸ hty1⟩
      exact ⟨y1,⟨(pA.not_mem_iff (hL.1.extreme_mem hy1.2 hy1L)).mp
          (fun hh => disjoint_left.mp pF.2.2.1 hh hy1.1),hy1.2⟩,
        y2,⟨(pA.not_mem_iff (hL.1.extreme_mem hy2.2 hy2L)).mp
          (fun hh => disjoint_left.mp pF.2.2.1 hh hy2.1),hy2.2⟩,he⟩
    · have hy1L : -y1 ∈ L := ⟨(extreme_unit_neg hy1.2).1,by simp [hty1]⟩
      have hy2L : -y2 ∈ L := ⟨(extreme_unit_neg hy2.2).1,by simp [← hty,hty1]⟩
      refine ⟨-y2,⟨(pA.not_mem_iff (hL.1.extreme_mem (extreme_unit_neg hy2.2) hy2L)).mp
          (fun hh => proper_unit_face_not_neg hmed hK.1 hK.2.1
            (pF.2.1.subset hy2.1) (pF.1.subset hh)),extreme_unit_neg hy2.2⟩,
        -y1,⟨(pA.not_mem_iff (hL.1.extreme_mem (extreme_unit_neg hy1.2) hy1L)).mp
          (fun hh => proper_unit_face_not_neg hmed hK.1 hK.2.1
            (pF.2.1.subset hy1.1) (pF.1.subset hh)),extreme_unit_neg hy1.2⟩,?_⟩
      linear_combination (norm := module) he
  apply mface_split_core hmed hdual hL pA hmF hmax q1 q2
    (eF1.symm ▸ hF1) (eF2.symm ▸ hF2) hmeetL hdisL hx1 hx2 hu1 hu2 _ _ heu
  · exact ⟨⟨hFL hx1.1,(eN1' ▸ hx1n.1).2⟩,hFL hx1.1,(eN2 ▸ hx1n.2).2⟩
  · exact ⟨⟨hFL hx2.1,(eN1 ▸ hx2n.1).2⟩,hFL hx2.1,(eN2' ▸ hx2n.2).2⟩

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem maximal_mface_split (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) {K F : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (hF : IsFace K F) (hmF : HasMFaceStructure F) (hmax : HasMaximalMRank F) :
    IsSplitFace K F := by
  by_contra hn
  obtain ⟨F',pF⟩ := maximal_mface_parallel hmed hK.1 hK.2.1 hF hmF hmax
  obtain ⟨x1,hx1,x2,hx2,y1,hy1,y2,hy2,hne,he⟩ :=
    nonsplit_vertex_parallelogram hmed hK.1 hK.2.1 pF hn
  have hFb := hK.1.trans hF
  have hFp := proper_unit_face_subface_ne hK.1 hK.2.1 hF.subset
  have hx1F := hFb.extreme_mem hx1.2 hx1.1
  have hx2F := hFb.extreme_mem hx2.2 hx2.1
  have hx1K := hK.1.extreme_mem hx1.2 (hF.subset hx1.1)
  have hx2K := hK.1.extreme_mem hx2.2 (hF.subset hx2.1)
  have hy1K := hK.1.extreme_mem hy1.2 (pF.2.1.subset hy1.1)
  have hy2K := hK.1.extreme_mem hy2.2 (pF.2.1.subset hy2.1)
  obtain ⟨F1,hF1,hx2F1,hx1F1⟩ := extend_face_avoiding_vertex hmed hFb hFp
    (IsFace.singleton hx2F) (singleton_nonempty x2) hx1F (by simpa using hne)
  have hx2F1 : x2 ∈ F1 := hx2F1 (mem_singleton _)
  obtain ⟨F1',pF1⟩ := maximal_proper_parallel hmed hFb hF1 ⟨_,hx2F1⟩
  have hx1F1' := (pF1.not_mem_iff hx1F).mp hx1F1
  have hx2F1' : x2 ∉ F1' := fun hh => disjoint_left.mp pF1.2.2.1 hx2F1 hh
  obtain ⟨F2,hF2,hF1'F2,hx2F2⟩ := extend_face_avoiding_vertex hmed hFb hFp
    pF1.2.1 ⟨_,hx1F1'⟩ hx2F hx2F1'
  have hx1F2 := hF1'F2 hx1F1'
  obtain ⟨F2',pF2⟩ := maximal_proper_parallel hmed hFb hF2 ⟨_,hx1F2⟩
  have hx2F2' := (pF2.not_mem_iff hx2F).mp hx2F2
  have hdis : Disjoint F1' F2' := disjoint_left.mpr
    (fun z hz hz' => disjoint_left.mp pF2.2.2.1 (hF1'F2 hz) hz')
  have hmeet : (F1 ∩ F2).Nonempty := by
    by_contra hn
    have hd : Disjoint F1 F2 := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
    obtain ⟨G,pG⟩ := (maximal_mface_children_parallel hmed hK.1 hK.2.1 pF hmax
      hF1 hF2 ⟨_,hx2F1⟩ ⟨_,hx1F2⟩ hd).1
    have hy1G := (pG.not_mem_iff hy1K).mp
      (fun hh => disjoint_left.mp pF.2.2.1 (hF1.1.subset hh) hy1.1)
    have hx1G := (pG.not_mem_iff hx1K).mp hx1F1
    have hx2G := (face_mem_of_parallelogram pG.2.1 hx1G hy1G hx2K.1 hy2K.1 he).1
    exact disjoint_left.mp pG.2.2.1 hx2F1 hx2G
  obtain ⟨f1,hf1,eF1,eF1'⟩ := pF1.support_dual_vertex hmed hFb ⟨_,hx2F1⟩ ⟨_,hx1F1'⟩
  obtain ⟨f2,hf2,eF2,eF2'⟩ := pF2.support_dual_vertex hmed hFb ⟨_,hx1F2⟩ ⟨_,hx2F2'⟩
  let N1 := {x ∈ K | f1 x=1}
  let N1' := {x ∈ K | f1 x= -1}
  let N2 := {x ∈ K | f2 x=1}
  let N2' := {x ∈ K | f2 x= -1}
  have p1 : IsParallelPair K N1 N1' := parallelPair_of_dual_vertex hmed hK.1 hf1
  have p2 : IsParallelPair K N2 N2' := parallelPair_of_dual_vertex hmed hK.1 hf2
  have e1 : F ∩ N1 = F1 := (IsParallelPair.restrict_support hF.subset rfl).trans eF1.symm
  have e2 : F ∩ N2 = F2 := (IsParallelPair.restrict_support hF.subset rfl).trans eF2.symm
  have e1' : F ∩ N1' = F1' := by
    rw [eF1']; ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hF.subset h.1,h.2⟩⟩
  have e2' : F ∩ N2' = F2' := by
    rw [eF2']; ext x
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hF.subset h.1,h.2⟩⟩
  have hmeetK : (F ∩ N1 ∩ N2).Nonempty := by
    obtain ⟨z,hz1,hz2⟩ := hmeet
    have hzN1 : z ∈ F ∩ N1 := e1.symm ▸ hz1
    have hzN2 : z ∈ F ∩ N2 := e2.symm ▸ hz2
    exact ⟨z,hzN1,hzN2.2⟩
  exact mface_split_precore hmed hdual hK pF hmF hmax p1 p2
    (e1.symm ▸ hF1) (e2.symm ▸ hF2) hmeetK (by rwa [e1',e2']) hx1 hx2 hy1 hy2
    ⟨⟨hx1K.1,(eF1' ▸ hx1F1').2⟩,hx1K.1,(eF2 ▸ hx1F2).2⟩
    ⟨⟨hx2K.1,(eF1 ▸ hx2F1).2⟩,hx2K.1,(eF2' ▸ hx2F2').2⟩ he

end
section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [inst541 : FiniteDimensional ℝ E] [inst542 : Nontrivial E]

omit inst541 inst542 in
lemma faceRank_singleton_le [FiniteDimensional ℝ E] [Nontrivial E] (a : E) : faceRank ({a} : Set E) ≤ 1 := by
  simpa [faceRank] using (finrank_span_le_card ({a} : Set E) (R := ℝ))

lemma mface_pair_obstruction (hmed : HasMetricMedians E) {L : Set E}
    (hL : IsFace (closedBall (0:E) 1) L) (hp : L ≠ closedBall (0:E) 1)
    (hr : 2 < faceRank L) (hm : HasMFaceStructure L)
    {a b : E} (ha : a ∈ L.extremePoints ℝ) (hb : b ∈ L.extremePoints ℝ)
    (hne : a ≠ b)
    (hn1 : ∀ g ∈ L ∩ (closedBall (0:E) 1).extremePoints ℝ,
      g ≠ a → g ≠ b → ∀ h ∈ closedBall (0:E) 1, a+g ≠ b+h)
    (hn2 : ∀ g ∈ L ∩ (closedBall (0:E) 1).extremePoints ℝ,
      g ≠ a → g ≠ b → ∀ h ∈ closedBall (0:E) 1, a+b ≠ g+h) : False := by
  have hav : a ∈ (closedBall (0:E) 1).extremePoints ℝ := hL.2.extremePoints_subset_extremePoints ha
  have hbv : b ∈ (closedBall (0:E) 1).extremePoints ℝ := hL.2.extremePoints_subset_extremePoints hb
  obtain ⟨H,H',hH,hH',hHn,hH'n,hHH',haH,hbH'⟩ :
      ∃ H H', IsMaximalProperFace L H ∧ IsMaximalProperFace L H' ∧
        H.Nonempty ∧ H'.Nonempty ∧ Disjoint H H' ∧ a ∈ H ∧ b ∈ H' := by
    obtain ⟨H,H',hH,hH',hHn,hH'n,hHH'⟩ := hm
    have p := maximal_pair_of_disjoint hmed hL hH hH' hHn hH'n hHH'
    have hnH : ¬ (a ∈ H ∧ b ∈ H) := by
      rintro ⟨haH,hbH⟩
      obtain ⟨g,hg,h,hh,he⟩ := hH'.exchange hmed hL p.symm hH'n ha haH hb hbH
      exact hn1 g ⟨hH'.1.subset hg.1,hg.2⟩
        (fun e => disjoint_left.mp hHH' haH (e ▸ hg.1))
        (fun e => disjoint_left.mp hHH' hbH (e ▸ hg.1)) h hh.2.1 he
    have hnH' : ¬ (a ∈ H' ∧ b ∈ H') := by
      rintro ⟨haH,hbH⟩
      obtain ⟨g,hg,h,hh,he⟩ := hH.exchange hmed hL p hHn ha haH hb hbH
      exact hn1 g ⟨hH.1.subset hg.1,hg.2⟩
        (fun e => disjoint_left.mp hHH' (e ▸ hg.1) haH)
        (fun e => disjoint_left.mp hHH' (e ▸ hg.1) hbH) h hh.2.1 he
    rcases p.vertex_mem ha with haH | haH
    · exact ⟨H,H',hH,hH',hHn,hH'n,hHH',haH,
        (p.not_mem_iff hb).mp (fun hbH => hnH ⟨haH,hbH⟩)⟩
    · exact ⟨H',H,hH',hH,hH'n,hHn,hHH'.symm,haH,
        (p.symm.not_mem_iff hb).mp (fun hbH => hnH' ⟨haH,hbH⟩)⟩
  have pH := maximal_pair_of_disjoint hmed hL hH hH' hHn hH'n hHH'
  let J := faceHull (closedBall (0:E) 1) ({a} ∪ {b})
  have hbase : {a} ∪ {b} ⊆ L := union_subset (singleton_subset_iff.mpr ha.1)
    (singleton_subset_iff.mpr hb.1)
  have hJ : IsFace (closedBall (0:E) 1) J :=
    isFace_faceHull (convex_closedBall _ _) (hbase.trans hL.subset)
  have hJL : J ⊆ L := faceHull_min hL hbase
  have haJ : a ∈ J := subset_faceHull (Or.inl (mem_singleton _))
  have hbJ : b ∈ J := subset_faceHull (Or.inr (mem_singleton _))
  have hJv : ∀ g ∈ (closedBall (0:E) 1).extremePoints ℝ ∩ J, g=a ∨ g=b := by
    intro g hg
    by_contra hn
    obtain ⟨h,hh,he⟩ := vertex_in_two_vertex_face hmed hav hbv hg.1 hg.2
    exact hn2 g ⟨hJL hg.2,hg.1⟩ (fun e => hn (Or.inl e))
      (fun e => hn (Or.inr e)) h hh.1 he
  have hHr := maximal_proper_rank hmed hL hp hH hHn
  have hHball := hL.trans hH.1
  have hHproper := proper_unit_face_subface_ne hL hp hH.1.subset
  have hHn1 : ¬ H ⊆ {a} := by
    intro hh
    have hle := (faceRank_mono hh).trans (faceRank_singleton_le a)
    omega
  obtain ⟨w,hw,hwH,hwa⟩ := hHball.exists_vertex_outside hmed (convex_singleton a) hHn1
  obtain ⟨N,hN,hwN,haN⟩ := extend_face_avoiding_vertex hmed hHball hHproper
    (IsFace.singleton (hHball.extreme_mem hw hwH)) (singleton_nonempty w)
    (hHball.extreme_mem hav haH) (by simpa [eq_comm] using hwa)
  have hwN : w ∈ N := hwN (mem_singleton _)
  have hNball := hHball.trans hN.1
  have hNJ : Disjoint N J := by
    by_contra hd
    obtain ⟨z,hz,hzN,hzJ⟩ := (hNball.inter hJ).exists_vertex hmed (not_disjoint_iff.mp hd)
    rcases hJv z ⟨hz,hzJ⟩ with rfl | rfl
    · exact haN hzN
    · exact disjoint_left.mp hHH' (hN.1.subset hzN) hbH'
  obtain ⟨f,hf,hfN,hfJ⟩ := disjoint_faces_dual_vertex hmed hNball hJ
    ⟨_,hwN⟩ ⟨_,haJ⟩ hNJ
  let M := {x ∈ L | f x=1}
  let M' := {x ∈ L | f x= -1}
  have pM : IsParallelPair L M M' := parallelPair_of_dual_vertex hmed hL hf
  have hNM : N ⊆ M := fun x hx => ⟨hH.1.subset (hN.1.subset hx),hfN x hx⟩
  have haM' : a ∈ M' := ⟨ha.1,hfJ a haJ⟩
  have hbM' : b ∈ M' := ⟨hb.1,hfJ b hbJ⟩
  have hMn : M.Nonempty := ⟨_,hNM hwN⟩
  have hMp : M ≠ L := pM.left_ne ⟨_,haM'⟩
  have hM'p : M' ≠ L := pM.symm.left_ne hMn
  have hMH' : (M ∩ H').Nonempty := by
    by_contra hn
    have hd : Disjoint H' M := (disjoint_iff_inter_eq_empty.mpr
      (not_nonempty_iff_eq_empty.mp hn)).symm
    have hsub := pM.subset_of_disjoint hmed hL hH'.1 hd
    have he := hH'.2.2 M' pM.2.1 hsub hM'p
    exact disjoint_left.mp hHH' haH (he ▸ haM')
  have hNm : N ≠ M := by
    intro he
    obtain ⟨x,hxM,hxH'⟩ := hMH'
    exact disjoint_left.mp hHH' (hN.1.subset (he.symm ▸ hxM)) hxH'
  have hNr := maximal_proper_rank hmed hHball hHproper hN ⟨_,hwN⟩
  have hNMrank := faceRank_lt hmed (hL.trans pM.1)
    (proper_unit_face_subface_ne hL hp pM.1.subset)
    (hNball.mono (hL.trans pM.1).subset hNM) hNm
  have hMrank := faceRank_lt hmed hL hp pM.1 hMp
  have hMm := rank_succ_maximal hmed hL hp pM.1 hMp (by omega)
  obtain ⟨g,hg,h,hh,he⟩ := hMm.exchange hmed hL pM hMn ha haM' hb hbM'
  exact hn1 g ⟨pM.1.subset hg.1,hg.2⟩
    (fun e => disjoint_left.mp pM.2.2.1 (e ▸ hg.1) haM')
    (fun e => disjoint_left.mp pM.2.2.1 (e ▸ hg.1) hbM') h hh.2.1 he

end

open Set Metric
open scoped Pointwise
section
variable {E : Type*} [NormedAddCommGroup E] [inst544 : NormedSpace ℝ E]

lemma IsFace.neg {K F : Set E} (h : IsFace K F) : IsFace (-K) (-F) := by
  refine ⟨h.1.neg,⟨fun x hx => h.subset hx,?_⟩⟩
  intro x hx y hy z hz hs
  apply h.2.left_mem_of_mem_openSegment hx hy hz
  obtain ⟨a,b,ha,hb,hab,he⟩ := hs
  refine ⟨a,b,ha,hb,hab,?_⟩
  rw [← he]
  module

lemma IsMaximalProperFace.neg {K F : Set E} (h : IsMaximalProperFace K F) :
    IsMaximalProperFace (-K) (-F) := by
  refine ⟨h.1.neg,fun he => h.2.1 (by simpa using congrArg Neg.neg he),?_⟩
  intro G hG hFG hp
  have hG' : IsFace K (-G) := by simpa using hG.neg
  have hFG' : F ⊆ -G := by
    intro x hx
    have hh := hFG (show -x ∈ -F by simpa using hx)
    simpa using hh
  have hp' : -G ≠ K := fun he => hp (by simpa using congrArg Neg.neg he)
  have he := h.2.2 (-G) hG' hFG' hp'
  simpa using congrArg Neg.neg he

lemma HasMFaceStructure.neg {F : Set E} (h : HasMFaceStructure F) : HasMFaceStructure (-F) := by
  obtain ⟨G,H,hG,hH,hGn,hHn,hd⟩ := h
  refine ⟨-G,-H,hG.neg,hH.neg,?_,?_,?_⟩
  · obtain ⟨g,hg⟩ := hGn
    exact ⟨-g,by simpa using hg⟩
  · obtain ⟨g,hg⟩ := hHn
    exact ⟨-g,by simpa using hg⟩
  · exact disjoint_left.mpr (fun x hx hy => disjoint_left.mp hd hx hy)

omit inst544 in
lemma neg_unitBall [NormedSpace ℝ E] : -(closedBall (0:E) 1) = closedBall (0:E) 1 := by
  ext x
  simp

lemma IsMaximalProperFace.neg_unit {K : Set E}
    (h : IsMaximalProperFace (closedBall (0:E) 1) K) :
    IsMaximalProperFace (closedBall (0:E) 1) (-K) := by
  simpa only [neg_unitBall] using h.neg

end

section
open Set Metric
open scoped Pointwise
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma maximal_unit_face_span (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty) :
    Submodule.span ℝ K = ⊤ := by
  obtain ⟨f,hf,he⟩ := maximal_unit_face_support hmed hK hn
  rw [he]
  exact span_support_dual_vertex hmed hf

lemma dual_eq_on_maximal_face (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    {f g : E →L[ℝ] ℝ} (he : ∀ x ∈ K, f x=g x) : f=g := by
  ext x
  apply LinearMap.eqOn_span (f:=f.toLinearMap) (g:=g.toLinearMap) he
  rw [maximal_unit_face_span hmed hK hn]
  trivial

lemma dual_vertex_eq_of_supports (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty)
    {f g : E →L[ℝ] ℝ}
    (hf : f ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (hg : g ∈ (closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints ℝ)
    (he : {x ∈ K | f x=1} = {x ∈ K | g x=1}) : f=g := by
  have hsub : K ⊆ (f-g).ker := by
    apply hK.1.subset_of_vertices hmed (Submodule.convex _)
    intro x hx
    change f x-g x=0
    rcases extreme_dual_eval_eq_one_or_neg_one hmed hx.1 hf with hfx | hfx
    · have hgx : g x=1 := (show x ∈ {x ∈ K | g x=1} from he ▸ ⟨hx.2,hfx⟩).2
      linarith
    · rcases extreme_dual_eval_eq_one_or_neg_one hmed hx.1 hg with hgx | hgx
      · have hfx' : f x=1 := (show x ∈ {x ∈ K | f x=1} from he.symm ▸ ⟨hx.2,hgx⟩).2
        linarith
      · linarith
  exact dual_eq_on_maximal_face hmed hK hn (fun x hx => sub_eq_zero.mp (hsub hx))

lemma dual_mface_obstruction_at_vertex (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 < Module.finrank ℝ E)
    {K : Set E} (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (hmK : HasMFaceStructure K) {x0 : E}
    (hx0 : x0 ∈ (closedBall (0:E) 1).extremePoints ℝ) (hx0K : x0 ∈ K)
    {L : Set (E →L[ℝ] ℝ)}
    (hL : IsMaximalProperFace (closedBall (0 : E →L[ℝ] ℝ) 1) L)
    (eL : L = {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | f x0=1})
    (hmL : HasMFaceStructure L) : False := by
  have hKn : K.Nonempty := ⟨_,hx0K⟩
  obtain ⟨a,ha,eK⟩ := maximal_unit_face_support hmed hK hKn
  obtain ⟨F,F',hF,hF',hFn,hF'n,hFF',hx0F⟩ :
      ∃ F F', IsMaximalProperFace K F ∧ IsMaximalProperFace K F' ∧
        F.Nonempty ∧ F'.Nonempty ∧ Disjoint F F' ∧ x0 ∈ F := by
    obtain ⟨F,F',hF,hF',hFn,hF'n,hFF'⟩ := hmK
    have p := maximal_pair_of_disjoint hmed hK.1 hF hF' hFn hF'n hFF'
    rcases p.vertex_mem (hK.1.extreme_mem hx0 hx0K) with hh | hh
    · exact ⟨F,F',hF,hF',hFn,hF'n,hFF',hh⟩
    · exact ⟨F',F,hF',hF,hF'n,hFn,hFF'.symm,hh⟩
  have pF := maximal_pair_of_disjoint hmed hK.1 hF hF' hFn hF'n hFF'
  obtain ⟨b,hb,eF,eF'⟩ := pF.support_dual_vertex hmed hK.1 hFn hF'n
  have haL : a ∈ L := by rw [eL]; exact ⟨ha.1,(eK ▸ hx0K).2⟩
  have hbL : b ∈ L := by rw [eL]; exact ⟨hb.1,(eF ▸ hx0F).2⟩
  have hab : a ≠ b := by
    intro he
    obtain ⟨x,hx⟩ := hF'n
    have h1 := (eK ▸ hF'.1.subset hx).2
    have h2 := (eF' ▸ hx).2
    rw [he] at h1
    linarith
  have hrd : 2 < faceRank L := by
    rw [maximal_unit_face_rank hdual hL ⟨_,haL⟩,finrank_strongDual]
    exact hdim
  apply mface_pair_obstruction hdual hL.1 hL.2.1 hrd hmL
    (hL.1.extreme_mem ha haL) (hL.1.extreme_mem hb hbL) hab
  · intro g hg hga hgb h hh he
    let G := {x ∈ K | g x=1}
    let G' := {x ∈ K | g x= -1}
    have pG : IsParallelPair K G G' := parallelPair_of_dual_vertex hmed hK.1 hg.2
    have hx0G : x0 ∈ G := ⟨hx0K,(eL ▸ hg.1).2⟩
    have hcross : (F' ∩ G).Nonempty := by
      by_contra hn
      have hd : Disjoint F' G := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
      have hsub := pG.subset_of_disjoint hmed hK.1 hF'.1 hd
      have heG' : G'=F' := hF'.2.2 G' pG.2.1 hsub (pG.symm.left_ne ⟨_,hx0G⟩)
      have heG : G=F := by
        rw [heG'] at pG
        exact pG.symm.complement_unique hmed hK.1 pF.symm
      apply hgb
      exact dual_vertex_eq_of_supports hmed hK hKn hg.2 hb (heG.trans eF)
    obtain ⟨x,hxF',hxG⟩ := hcross
    have hax := (eK ▸ hF'.1.subset hxF').2
    have hbx := (eF' ▸ hxF').2
    have hhx := dual_eval_bounds (mem_closedBall_zero_iff.mp hh) (hK.1.subset hxG.1)
    have hhe := congrArg (fun f : E →L[ℝ] ℝ => f x) he
    change a x+g x=b x+h x at hhe
    linarith [hxG.2]
  · intro g hg hga hgb h hh he
    let G := {x ∈ K | g x=1}
    let G' := {x ∈ K | g x= -1}
    have pG : IsParallelPair K G G' := parallelPair_of_dual_vertex hmed hK.1 hg.2
    have hGp : G ≠ K := by
      intro heG
      apply hga
      apply dual_eq_on_maximal_face hmed hK hKn
      intro x hx
      exact (heG.symm ▸ hx).2.trans (eK ▸ hx).2.symm
    have hcross : (F ∩ G').Nonempty := by
      by_contra hn
      have hd : Disjoint F G' := disjoint_iff_inter_eq_empty.mpr (not_nonempty_iff_eq_empty.mp hn)
      have hsub := pG.symm.subset_of_disjoint hmed hK.1 hF.1 hd
      have heG : G=F := hF.2.2 G pG.1 hsub hGp
      exact hgb (dual_vertex_eq_of_supports hmed hK hKn hg.2 hb (heG.trans eF))
    obtain ⟨x,hxF,hxG'⟩ := hcross
    have hax := (eK ▸ hF.1.subset hxF).2
    have hbx := (eF ▸ hxF).2
    have hhx := dual_eval_bounds (mem_closedBall_zero_iff.mp hh) (hK.1.subset hxG'.1)
    have hhe := congrArg (fun f : E →L[ℝ] ℝ => f x) he
    change a x+b x=g x+h x at hhe
    linarith [hxG'.2]

theorem not_primal_dual_maximal_mfaces (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 < Module.finrank ℝ E)
    {K : Set E} (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (hmK : HasMFaceStructure K)
    {L : Set (E →L[ℝ] ℝ)}
    (hL : IsMaximalProperFace (closedBall (0 : E →L[ℝ] ℝ) 1) L)
    (hmL : HasMFaceStructure L) : False := by
  obtain ⟨A,B,hA,hB,hAn,hBn,hAB⟩ := hmL
  have hLn : L.Nonempty := hAn.mono hA.1.subset
  obtain ⟨u,hu,he⟩ := maximal_unit_face_support hdual hL hLn
  rw [← LinearIsometryEquiv.image_extreme_unit (finiteBidual (E:=E))] at hu
  obtain ⟨x0,hx0,rfl⟩ := hu
  change L = {f ∈ closedBall (0 : E →L[ℝ] ℝ) 1 | f x0=1} at he
  have hKn : K.Nonempty := by
    obtain ⟨A,B,hA,hB,hAn,hBn,hAB⟩ := hmK
    exact hAn.mono hA.1.subset
  rcases maximal_unit_face_vertex_sign hmed hK hKn hx0 with hxK | hxK
  · exact dual_mface_obstruction_at_vertex hmed hdual hdim hK hmK hx0 hxK hL he
      ⟨A,B,hA,hB,hAn,hBn,hAB⟩
  · exact dual_mface_obstruction_at_vertex hmed hdual hdim hK.neg_unit hmK.neg hx0 hxK
      hL he ⟨A,B,hA,hB,hAn,hBn,hAB⟩

end

open Set Metric
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

lemma face_rank_gt_one_vertices (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hr : 1 < faceRank K) :
    ∃ x ∈ K.extremePoints ℝ, ∃ y ∈ K.extremePoints ℝ, x ≠ y := by
  have hn : K.Nonempty := by
    by_contra hh
    rw [not_nonempty_iff_eq_empty.mp hh,faceRank,Submodule.span_empty,finrank_bot] at hr
    omega
  obtain ⟨x,hx,hxK⟩ := hK.exists_vertex hmed hn
  have hnot : ¬ K ⊆ {x} := by
    intro hh
    have := (faceRank_mono hh).trans (faceRank_singleton_le x)
    omega
  obtain ⟨y,hy,hyK,hyn⟩ := hK.exists_vertex_outside hmed (convex_singleton x) hnot
  exact ⟨x,hK.extreme_mem hx hxK,y,hK.extreme_mem hy hyK,by simpa [eq_comm] using hyn⟩

lemma face_rank_two_pair (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hr : faceRank K = 2) :
    ∃ F G, IsSplitPair K F G ∧ IsMaximalProperFace K F ∧
      IsMaximalProperFace K G ∧ F.Nonempty ∧ G.Nonempty := by
  obtain ⟨x,hx,y,hy,hxy⟩ := face_rank_gt_one_vertices hmed hK (by omega)
  obtain ⟨F,hF,hxF,hyF⟩ := extend_face_avoiding_vertex hmed hK hp
    (IsFace.singleton hx) (singleton_nonempty x) hy (by simpa [eq_comm] using hxy)
  have hxF' := hxF (mem_singleton x)
  have hFn : F.Nonempty := ⟨_,hxF'⟩
  have hrF := maximal_proper_rank hmed hK hp hF hFn
  have eF : F = {x} := by
    by_contra hn
    have hs := (IsFace.singleton hx).mono hF.1.subset hxF
    have := faceRank_lt hmed (hK.trans hF.1)
      (proper_unit_face_subface_ne hK hp hF.1.subset) hs (Ne.symm hn)
    have hpos : 0 < faceRank ({x} : Set E) := by
      have hn0 : x ≠ 0 := by
        intro hh
        have := norm_eq_one_of_mem_proper_face hK.2 hp hx.1
        simp [hh] at this
      simp [faceRank,finrank_span_singleton hn0]
    omega
  obtain ⟨G,p⟩ := maximal_proper_parallel hmed hK hF hFn
  have hyG := (p.not_mem_iff hy).mp hyF
  have hGn : G.Nonempty := ⟨_,hyG⟩
  have hGp := p.symm.left_ne hFn
  have hGr := faceRank_lt hmed hK hp p.2.1 hGp
  have hGpos : 0 < faceRank G := by
    have hs := faceRank_mono (singleton_subset_iff.mpr hyG)
    have hy0 : y ≠ 0 := by
      intro hh
      have := norm_eq_one_of_mem_proper_face hK.2 hp hy.1
      simp [hh] at this
    have : faceRank ({y} : Set E) = 1 := by simp [faceRank,finrank_span_singleton hy0]
    omega
  have hmG := rank_succ_maximal hmed hK hp p.2.1 hGp (by omega)
  refine ⟨F,G,⟨p,split_of_no_vertex_parallelogram hmed hK hp p ?_⟩,hF,hmG,hFn,hGn⟩
  intro a ha b hb c hc d hd he
  rw [eF] at ha hb
  exact (mem_singleton_iff.mp ha.1).trans (mem_singleton_iff.mp hb.1).symm

lemma exists_rank_two_face (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsFace (closedBall (0:E) 1) K) (hp : K ≠ closedBall (0:E) 1)
    (hr : 2 ≤ faceRank K) :
    ∃ F, IsFace K F ∧ faceRank F = 2 := by
  generalize he : faceRank K = r
  induction r using Nat.strong_induction_on generalizing K with
  | h r ih =>
    by_cases he2 : faceRank K = 2
    · exact ⟨K,IsFace.refl hK.1,he2⟩
    obtain ⟨x,hx,y,hy,hxy⟩ := face_rank_gt_one_vertices hmed hK (by omega)
    obtain ⟨F,hF,hxF,hyF⟩ := extend_face_avoiding_vertex hmed hK hp
      (IsFace.singleton hx) (singleton_nonempty x) hy (by simpa [eq_comm] using hxy)
    have hFr := maximal_proper_rank hmed hK hp hF ⟨_,hxF (mem_singleton x)⟩
    obtain ⟨G,hG,hrG⟩ := ih (faceRank F) (by omega) (hK.trans hF.1)
      (proper_unit_face_subface_ne hK hp hF.1.subset) (by omega) rfl
    exact ⟨G,hF.1.trans hG,hrG⟩

lemma exists_maximal_unit_face (hmed : HasMetricMedians E) :
    ∃ K, IsMaximalProperFace (closedBall (0:E) 1) K ∧ K.Nonempty := by
  obtain ⟨f,hf⟩ := (isCompact_closedBall (0 : E →L[ℝ] ℝ) 1).extremePoints_nonempty
    ⟨0,by simp⟩
  refine ⟨_,dual_vertex_maximal_support hmed hf,?_⟩
  by_contra hn
  have hs := span_support_dual_vertex hmed hf
  rw [not_nonempty_iff_eq_empty.mp hn,Submodule.span_empty] at hs
  exact bot_ne_top hs

lemma exists_maximal_mface (hmed : HasMetricMedians E) (hdim : 2 ≤ Module.finrank ℝ E) :
    ∃ F, IsFace (closedBall (0:E) 1) F ∧ F ≠ closedBall (0:E) 1 ∧
      HasMFaceStructure F ∧ HasMaximalMRank F ∧ 2 ≤ faceRank F := by
  classical
  obtain ⟨K,hK,hKn⟩ := exists_maximal_unit_face hmed
  have hKr := maximal_unit_face_rank hmed hK hKn
  obtain ⟨F,hFK,hFr⟩ := exists_rank_two_face hmed hK.1 hK.2.1 (by omega)
  have hF := hK.1.trans hFK
  have hp := proper_unit_face_subface_ne hK.1 hK.2.1 hFK.subset
  obtain ⟨A,B,p,hA,hB,hAn,hBn⟩ := face_rank_two_pair hmed hF hp hFr
  have hmF : HasMFaceStructure F := ⟨A,B,hA,hB,hAn,hBn,p.1.2.2.1⟩
  let D := {F : Set E | IsFace (closedBall (0:E) 1) F ∧
    F ≠ closedBall (0:E) 1 ∧ HasMFaceStructure F}
  have hDf : D.Finite := (finite_unit_faces_of_medians hmed).subset (fun F hF => hF.1)
  obtain ⟨G,hG,hmax⟩ := Set.exists_max_image D faceRank hDf ⟨F,hF,hp,hmF⟩
  exact ⟨G,hG.1,hG.2.1,hG.2.2,fun L hL hpL hmL => hmax L ⟨hL,hpL,hmL⟩,
    by have := hmax F ⟨hF,hp,hmF⟩; omega⟩

lemma proper_split_of_no_maximal_mface (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 ≤ Module.finrank ℝ E)
    (hn : ∀ K, IsMaximalProperFace (closedBall (0:E) 1) K → ¬ HasMFaceStructure K) :
    ∃ K F G, IsMaximalProperFace (closedBall (0:E) 1) K ∧
      IsSplitPair K F G ∧ F.Nonempty ∧ G.Nonempty := by
  obtain ⟨F,hF,hp,hm,hmax,hr⟩ := exists_maximal_mface hmed hdim
  obtain ⟨A,B,hA,hB,hAn,hBn,hAB⟩ := hm
  have hFn := hAn.mono hA.1.subset
  obtain ⟨f,hf,hfF⟩ := proper_face_support hmed hF hFn hp
  let K := {x ∈ closedBall (0:E) 1 | f x=1}
  have hK : IsMaximalProperFace (closedBall (0:E) 1) K := dual_vertex_maximal_support hmed hf
  have hFK : F ⊆ K := fun x hx => ⟨hF.subset hx,hfF x hx⟩
  have hne : F ≠ K := by
    intro he
    exact hn K hK (he ▸ ⟨A,B,hA,hB,hAn,hBn,hAB⟩)
  obtain ⟨G,p⟩ := maximal_mface_split hmed hdual hK (hF.mono hK.1.subset hFK)
    ⟨A,B,hA,hB,hAn,hBn,hAB⟩ hmax
  refine ⟨K,F,G,hK,p,hFn,?_⟩
  by_contra hg
  have heG := not_nonempty_iff_eq_empty.mp hg
  have he := p.1.2.2.2
  rw [heG,union_empty,hF.1.convexHull_eq] at he
  exact hne he.symm

end SymmetricMahler

end

end OAI
end

section
-- module Solutions.OAIQ2_Mah.Mahler_Classification
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace SymmetricMahler

open Set Metric

section
variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

variable {E} [FiniteDimensional ℝ E] [Nontrivial E]

lemma maximal_unit_face_hull (hmed : HasMetricMedians E) {K : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K) (hn : K.Nonempty) :
    closedBall (0:E) 1 = convexHull ℝ (K ∪ -K) := by
  apply subset_antisymm
  · rw [unitBall_eq_convexHull_extreme hmed]
    apply convexHull_mono
    intro x hx
    rcases maximal_unit_face_vertex_sign hmed hK hn hx with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by simpa using hh)
  · apply convexHull_min _ (convex_closedBall _ _)
    rintro x (hx | hx)
    · exact hK.1.subset hx
    · have hx' : -x ∈ K := by simpa using hx
      simpa using hK.1.subset hx'

lemma norm_add_of_split (hmed : HasMetricMedians E) {K F G : Set E}
    (hK : IsMaximalProperFace (closedBall (0:E) 1) K)
    (p : IsSplitPair K F G) (hFn : F.Nonempty) (hGn : G.Nonempty) :
    Nonempty (LDecomposition E) := by
  let U := Submodule.span ℝ F
  let V := Submodule.span ℝ G
  have hKn := hFn.mono p.1.1.subset
  have hsup : U ⊔ V = ⊤ := by
    apply top_unique
    rw [← maximal_unit_face_span hmed hK hKn]
    apply Submodule.span_le.mpr
    rw [p.1.2.2.2]
    apply convexHull_min _ (Submodule.convex _)
    exact union_subset (fun _ hx => (show U ≤ U ⊔ V from le_sup_left) (Submodule.subset_span hx))
      (fun _ hx => (show V ≤ U ⊔ V from le_sup_right) (Submodule.subset_span hx))
  have hcompl : IsCompl U V := ⟨p.2,codisjoint_iff.mpr hsup⟩
  let e := Submodule.prodEquivOfIsCompl U V hcompl
  let C : Set E := {x | ‖(e.symm x).1‖+‖(e.symm x).2‖ ≤ 1}
  have hC : Convex ℝ C := by
    intro x hx y hy a b ha hb hab
    change ‖(e.symm (a • x+b • y)).1‖+‖(e.symm (a • x+b • y)).2‖ ≤ 1
    simp only [map_add,map_smul,Prod.fst_add,Prod.smul_fst,Prod.snd_add,Prod.smul_snd]
    have h1 := norm_add_le (a • (e.symm x).1) (b • (e.symm y).1)
    have h2 := norm_add_le (a • (e.symm x).2) (b • (e.symm y).2)
    simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb] at h1 h2
    have h3 := mul_le_mul_of_nonneg_left hx ha
    have h4 := mul_le_mul_of_nonneg_left hy hb
    change a * (‖(e.symm x).1‖+‖(e.symm x).2‖) ≤ a*1 at h3
    change b * (‖(e.symm y).1‖+‖(e.symm y).2‖) ≤ b*1 at h4
    nlinarith
  have hFC : F ⊆ C := by
    intro x hx
    have he : e.symm x = (⟨x,Submodule.subset_span hx⟩,0) :=
      Submodule.prodEquivOfIsCompl_symm_apply_left U V hcompl ⟨x,Submodule.subset_span hx⟩
    change ‖(e.symm x).1‖+‖(e.symm x).2‖ ≤ 1
    rw [he]
    simpa using mem_closedBall_zero_iff.mp (hK.1.subset (p.1.1.subset hx))
  have hGC : G ⊆ C := by
    intro x hx
    have he : e.symm x = (0,⟨x,Submodule.subset_span hx⟩) :=
      Submodule.prodEquivOfIsCompl_symm_apply_right U V hcompl ⟨x,Submodule.subset_span hx⟩
    change ‖(e.symm x).1‖+‖(e.symm x).2‖ ≤ 1
    rw [he]
    simpa using mem_closedBall_zero_iff.mp (hK.1.subset (p.1.2.1.subset hx))
  have hKC : K ⊆ C := by
    rw [p.1.2.2.2]
    exact convexHull_min (union_subset hFC hGC) hC
  have hBC : closedBall (0:E) 1 ⊆ C := by
    rw [maximal_unit_face_hull hmed hK hKn]
    apply convexHull_min _ hC
    rintro x (hx | hx)
    · exact hKC hx
    · have hh := hKC (show -x ∈ K by simpa using hx)
      simpa [C] using hh
  have heNorm : ∀ z, ‖e z‖ = ‖z.1‖+‖z.2‖ := by
    intro z
    apply le_antisymm
    · exact norm_add_le (z.1:E) (z.2:E)
    · by_cases hz : e z = 0
      · have hz' : z=0 := e.injective (by simpa using hz)
        simp [hz']
      have hp : 0 < ‖e z‖ := norm_pos_iff.mpr hz
      have hx : ‖e z‖⁻¹ • e z ∈ closedBall (0:E) 1 := by
        rw [mem_closedBall_zero_iff,norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)]
        simp [hp.ne']
      have hh := hBC hx
      change ‖(e.symm (‖e z‖⁻¹ • e z)).1‖+‖(e.symm (‖e z‖⁻¹ • e z)).2‖ ≤ 1 at hh
      simp only [map_smul,e.symm_apply_apply,Prod.smul_fst,Prod.smul_snd,norm_smul,
        Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hp)] at hh
      have hh' : (‖z.1‖+‖z.2‖) / ‖e z‖ ≤ 1 := by
        simpa only [div_eq_mul_inv,mul_add,add_mul,mul_comm] using hh
      exact (div_le_one hp).mp hh'
  exact ⟨⟨U,V,e,heNorm,(hK.1.trans p.1.1).rank_pos hmed
    (proper_unit_face_subface_ne hK.1 hK.2.1 p.1.1.subset) hFn,
    (hK.1.trans p.1.2.1).rank_pos hmed
    (proper_unit_face_subface_ne hK.1 hK.2.1 p.1.2.1.subset) hGn⟩⟩

end

section

lemma HasMetricMedians.of_retract {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (h : HasMetricMedians X) (i : Y → X) (p : X → Y)
    (hi : ∀ a b, dist (i a) (i b) ≤ dist a b)
    (hp : ∀ a b, dist (p a) (p b) ≤ dist a b)
    (hpi : ∀ a, p (i a)=a) : HasMetricMedians Y := by
  have he : ∀ a b, dist (i a) (i b)=dist a b := by
    intro a b
    exact le_antisymm (hi a b) (by simpa [hpi] using hp (i a) (i b))
  intro x
  obtain ⟨m,hm⟩ := h (i ∘ x)
  refine ⟨p m,fun a b hab => ?_⟩
  have h1 := hp (i (x a)) m
  have h2 := hp m (i (x b))
  have h3 := hm a b hab
  simp only [Function.comp_apply,he] at h3
  simp only [hpi] at h1 h2
  have h4 := dist_triangle (x a) (p m) (x b)
  linarith

lemma HasMetricMedians.linearIsometryEquiv {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : HasMetricMedians E) (e : E ≃ₗᵢ[ℝ] F) : HasMetricMedians F := by
  exact h.of_retract e.symm e (fun a b => (e.symm.dist_map a b).le)
    (fun a b => (e.dist_map a b).le) e.apply_symm_apply

lemma continuousLinearMap_dist_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E →L[ℝ] F) (hp : ∀ x, ‖p x‖ ≤ ‖x‖) (a b : E) :
    dist (p a) (p b) ≤ dist a b := by
  simpa only [dist_eq_norm,map_sub] using hp (a-b)

lemma dual_comp_dist_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : E →L[ℝ] F) (hp : ∀ x, ‖p x‖ ≤ ‖x‖) (a b : F →L[ℝ] ℝ) :
    dist (a.comp p) (b.comp p) ≤ dist a b := by
  have hpn : ‖p‖ ≤ 1 := p.opNorm_le_bound zero_le_one (by simpa using hp)
  have hh := (a-b).opNorm_comp_le p
  have hh' := mul_le_mul_of_nonneg_left hpn (norm_nonneg (a-b))
  rw [dist_eq_norm,dist_eq_norm]
  calc
    ‖a.comp p-b.comp p‖ = ‖(a-b).comp p‖ := by rfl
    _ ≤ ‖a-b‖*‖p‖ := hh
    _ ≤ ‖a-b‖ := by simpa using hh'

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]

namespace LDecomposition
variable (d : LDecomposition E)

lemma finrank_add : Module.finrank ℝ d.left + Module.finrank ℝ d.right = Module.finrank ℝ E := by
  rw [← Module.finrank_prod]
  exact d.equiv.finrank_eq

lemma left_lt : Module.finrank ℝ d.left < Module.finrank ℝ E := by
  have := d.finrank_add
  have := d.right_pos
  omega

lemma right_lt : Module.finrank ℝ d.right < Module.finrank ℝ E := by
  have := d.finrank_add
  have := d.left_pos
  omega

lemma norm_leftInclusion (x : d.left) : ‖d.leftInclusion x‖ = ‖x‖ := by
  change ‖d.equiv (x,0)‖=‖x‖
  simpa using d.norm_add (x,0)

lemma norm_leftProjection_le (x : E) : ‖d.leftProjection x‖ ≤ ‖x‖ := by
  have he := d.norm_add (d.equiv.symm x)
  rw [d.equiv.apply_symm_apply] at he
  change ‖(d.equiv.symm x).1‖ ≤ ‖x‖
  linarith [norm_nonneg (d.equiv.symm x).2]

lemma left_medians (h : HasMetricMedians E) : HasMetricMedians d.left :=
  h.of_retract d.leftInclusion d.leftProjection
    (continuousLinearMap_dist_le _ (fun x => (d.norm_leftInclusion x).le))
    (continuousLinearMap_dist_le _ d.norm_leftProjection_le) d.leftProjection_leftInclusion

lemma left_dual_medians (h : HasMetricMedians (E →L[ℝ] ℝ)) :
    HasMetricMedians (d.left →L[ℝ] ℝ) := by
  apply h.of_retract (fun f => f.comp d.leftProjection) (fun f => f.comp d.leftInclusion)
  · exact dual_comp_dist_le _ d.norm_leftProjection_le
  · exact dual_comp_dist_le _ (fun x => (d.norm_leftInclusion x).le)
  · intro f
    ext x
    simp

lemma right_medians (h : HasMetricMedians E) : HasMetricMedians d.right :=
  d.swap.left_medians h

lemma right_dual_medians (h : HasMetricMedians (E →L[ℝ] ℝ)) :
    HasMetricMedians (d.right →L[ℝ] ℝ) := d.swap.left_dual_medians h
end LDecomposition

end

section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma HannerSpace.linearIsometryEquiv (h : HannerSpace E) (e : E ≃ₗᵢ[ℝ] F) :
    HannerSpace F := by
  obtain ⟨n,H,hH,f,hf⟩ := h
  refine ⟨n,H,hH,f.trans e.toLinearEquiv,?_⟩
  change closedBall (0:F) 1 = (fun x => e (f x)) '' H
  rw [← image_image,← hf,e.image_closedBall,map_zero]

lemma hannerSpace_one [FiniteDimensional ℝ E] (hd : Module.finrank ℝ E = 1) :
    HannerSpace E := by
  let e : (Fin 1 → ℝ) ≃ₗ[ℝ] E := LinearEquiv.ofFinrankEq _ _ (by simpa using hd.symm)
  let u : Fin 1 → ℝ := fun _ => 1
  have hu : e u ≠ 0 := by
    intro hh
    have : u=0 := e.injective (by simpa using hh)
    have hh := congrFun this 0
    norm_num [u] at hh
  have hp : 0 < ‖e u‖ := norm_pos_iff.mpr hu
  have he (x : Fin 1 → ℝ) : ‖e x‖ = |x 0| * ‖e u‖ := by
    have hx : x = x 0 • u := by ext i; fin_cases i; simp [u]
    conv_lhs => rw [hx]
    rw [map_smul,norm_smul,Real.norm_eq_abs]
  refine ⟨1,_,IsHanner.interval (‖e u‖⁻¹) (inv_pos.mpr hp),e,?_⟩
  ext y
  obtain ⟨x,rfl⟩ := e.surjective y
  rw [e.injective.mem_set_image,mem_closedBall_zero_iff,he]
  simp only [mem_Icc,Pi.le_def,Fin.forall_fin_one]
  rw [← abs_le,← one_div]
  exact (le_div_iff₀ hp).symm

lemma dual_norm_le_one_iff (f : E →L[ℝ] ℝ) :
    ‖f‖ ≤ 1 ↔ ∀ x ∈ closedBall (0:E) 1, f x ≤ 1 := by
  constructor
  · intro hf x hx
    have hxn := mem_closedBall_zero_iff.mp hx
    exact (le_abs_self (f x)).trans <| (f.le_opNorm x).trans <|
      (mul_le_mul hf hxn (norm_nonneg x) zero_le_one).trans_eq (mul_one 1)
  · intro hf
    apply ContinuousLinearMap.opNorm_le_of_unit_norm zero_le_one
    intro x hx
    rw [Real.norm_eq_abs,abs_le]
    have hh := hf (-x) (by simp [hx])
    simpa using And.intro (by linarith [show f (-x) = -f x from map_neg f x])
      (hf x (by simp [hx]))

lemma HannerSpace.dual [FiniteDimensional ℝ E] (h : HannerSpace E) :
    HannerSpace (E →L[ℝ] ℝ) := by
  obtain ⟨n,H,hH,e,he⟩ := h
  refine ⟨n,coordinatePolar H,hH.polar,coordinateDual e,?_⟩
  ext f
  obtain ⟨p,rfl⟩ := (coordinateDual e).surjective f
  rw [(coordinateDual e).injective.mem_set_image,mem_closedBall_zero_iff,
    dual_norm_le_one_iff,he]
  constructor
  · intro hh x hx
    simpa only [coordinateDual_apply] using hh (e x) (mem_image_of_mem e hx)
  · intro hh y hy
    obtain ⟨x,hx,rfl⟩ := hy
    simpa only [coordinateDual_apply] using hh x hx

end

section

lemma normData_unit (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    (normData E).unit = closedBall (0:E) 1 := by
  ext x
  exact mem_closedBall_zero_iff.symm

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma LDecomposition.unitBall (d : LDecomposition E) :
    closedBall (0:E) 1 = d.equiv '' convexHull ℝ
      (((fun x : d.left => (x,(0:d.right))) '' closedBall (0:d.left) 1) ∪
        ((fun y : d.right => ((0:d.left),y)) '' closedBall (0:d.right) 1)) := by
  rw [← normData_unit d.left,← normData_unit d.right,← RealNormData.unit_sum]
  ext x
  obtain ⟨z,rfl⟩ := d.equiv.surjective x
  rw [d.equiv.injective.mem_set_image,mem_closedBall_zero_iff,d.norm_add]
  rfl

lemma LDecomposition.hannerSpace (d : LDecomposition E)
    (hU : HannerSpace d.left) (hV : HannerSpace d.right) : HannerSpace E := by
  obtain ⟨k,A,hA,eu,heu⟩ := hU
  obtain ⟨l,B,hB,ev,hev⟩ := hV
  let e : (Fin (k+l) → ℝ) ≃ₗ[ℝ] E :=
    (appendEquiv k l).symm.trans ((eu.prodCongr ev).trans d.equiv)
  have h1 (x : Fin k → ℝ) : e (Fin.append x 0) = d.equiv (eu x,0) := by
    change d.equiv ((eu.prodCongr ev) ((appendEquiv k l).symm (appendEquiv k l (x,0)))) = _
    rw [(appendEquiv k l).symm_apply_apply]
    simp
  have h2 (y : Fin l → ℝ) : e (Fin.append 0 y) = d.equiv (0,ev y) := by
    change d.equiv ((eu.prodCongr ev) ((appendEquiv k l).symm (appendEquiv k l (0,y)))) = _
    rw [(appendEquiv k l).symm_apply_apply]
    simp
  refine ⟨k+l,hannerJoin A B,IsHanner.join hA hB,e,?_⟩
  rw [d.unitBall,heu,hev]
  change d.equiv.toLinearMap '' convexHull ℝ _ = e.toLinearMap '' convexHull ℝ _
  rw [LinearMap.image_convexHull,LinearMap.image_convexHull]
  congr 1
  simp only [image_union,image_image]
  congr 1
  · congr 1
    funext x
    exact (h1 x).symm
  · congr 1
    funext y
    exact (h2 y).symm

end

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E] [Nontrivial E]

theorem median_decomposition (hmed : HasMetricMedians E)
    (hdual : HasMetricMedians (E →L[ℝ] ℝ)) (hdim : 2 ≤ Module.finrank ℝ E) :
    Nonempty (LDecomposition E) ∨ Nonempty (LDecomposition (E →L[ℝ] ℝ)) := by
  classical
  by_cases hd2 : Module.finrank ℝ E = 2
  · obtain ⟨K,hK,hKn⟩ := exists_maximal_unit_face hmed
    have hr : faceRank K = 2 := (maximal_unit_face_rank hmed hK hKn).trans hd2
    obtain ⟨F,G,p,-,-,hFn,hGn⟩ := face_rank_two_pair hmed hK.1 hK.2.1 hr
    exact Or.inl (norm_add_of_split hmed hK p hFn hGn)
  by_cases hh : ∃ K, IsMaximalProperFace (closedBall (0:E) 1) K ∧ HasMFaceStructure K
  · obtain ⟨K,hK,hmK⟩ := hh
    have hbi : HasMetricMedians ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
      HasMetricMedians.linearIsometryEquiv (E:=E) (F:=((E →L[ℝ] ℝ) →L[ℝ] ℝ))
        hmed (finiteBidual (E:=E))
    have hn : ∀ L, IsMaximalProperFace (closedBall (0 : E →L[ℝ] ℝ) 1) L →
        ¬ HasMFaceStructure L := by
      intro L hL hmL
      exact not_primal_dual_maximal_mfaces hmed hdual (by omega) hK hmK hL hmL
    obtain ⟨L,F,G,hL,p,hFn,hGn⟩ := proper_split_of_no_maximal_mface hdual hbi
      (by rwa [finrank_strongDual]) hn
    exact Or.inr (norm_add_of_split hdual hL p hFn hGn)
  · have hn : ∀ K, IsMaximalProperFace (closedBall (0:E) 1) K → ¬ HasMFaceStructure K := by
      intro K hK hmK
      exact hh ⟨K,hK,hmK⟩
    obtain ⟨K,F,G,hK,p,hFn,hGn⟩ := proper_split_of_no_maximal_mface hmed hdual hdim hn
    exact Or.inl (norm_add_of_split hmed hK p hFn hGn)

end
section

universe u

private theorem hannerSpace_of_medians_rank (n : ℕ) :
    ∀ (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [Nontrivial E], Module.finrank ℝ E = n →
      HasMetricMedians E → HasMetricMedians (E →L[ℝ] ℝ) → HannerSpace E := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro E _ _ _ _ he hmed hdual
    by_cases hn : n = 1
    · exact hannerSpace_one (he.trans hn)
    have hp : 0 < Module.finrank ℝ E := Module.finrank_pos
    have hd : 2 ≤ Module.finrank ℝ E := by omega
    rcases median_decomposition hmed hdual hd with hd | hd
    · obtain ⟨d⟩ := hd
      let : Nontrivial d.left := Module.finrank_pos_iff.mp d.left_pos
      let : Nontrivial d.right := Module.finrank_pos_iff.mp d.right_pos
      apply d.hannerSpace
      · exact ih _ (by have := d.left_lt; omega) d.left rfl
          (d.left_medians hmed) (d.left_dual_medians hdual)
      · exact ih _ (by have := d.right_lt; omega) d.right rfl
          (d.right_medians hmed) (d.right_dual_medians hdual)
    · obtain ⟨d⟩ := hd
      let : Nontrivial d.left := Module.finrank_pos_iff.mp d.left_pos
      let : Nontrivial d.right := Module.finrank_pos_iff.mp d.right_pos
      have hbi : HasMetricMedians ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
        HasMetricMedians.linearIsometryEquiv (E:=E) (F:=((E →L[ℝ] ℝ) →L[ℝ] ℝ))
          hmed (finiteBidual (E:=E))
      have he' : Module.finrank ℝ (E →L[ℝ] ℝ) = n := finrank_strongDual.trans he
      have hh : HannerSpace (E →L[ℝ] ℝ) := d.hannerSpace
        (ih _ (by have := d.left_lt; omega) d.left rfl
          (d.left_medians hdual) (d.left_dual_medians hbi))
        (ih _ (by have := d.right_lt; omega) d.right rfl
          (d.right_medians hdual) (d.right_dual_medians hbi))
      exact HannerSpace.linearIsometryEquiv (E:=((E →L[ℝ] ℝ) →L[ℝ] ℝ)) (F:=E)
        hh.dual (finiteBidual (E:=E)).symm

theorem hannerSpace_of_medians {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E]
    (hmed : HasMetricMedians E) (hdual : HasMetricMedians (E →L[ℝ] ℝ)) : HannerSpace E :=
  hannerSpace_of_medians_rank _ E rfl hmed hdual

namespace RealNormData

lemma hannerSpace_iff_linearHanner {n : ℕ} (g : RealNormData (Fin n → ℝ)) :
    HannerSpace g.Space ↔ IsLinearHanner g.unit := by
  constructor
  · rintro ⟨m,H,hH,e,he⟩
    have hmn : m=n := by simpa using (e.trans g.spaceEquiv).finrank_eq
    subst m
    refine ⟨H,hH,e.trans g.spaceEquiv,?_⟩
    rw [g.unit_eq_image_closedBall,he,image_image]
    rfl
  · rintro ⟨H,hH,e,he⟩
    refine ⟨n,H,hH,e.trans g.spaceEquiv.symm,?_⟩
    apply (Set.image_injective.mpr g.spaceEquiv.injective)
    rw [← g.unit_eq_image_closedBall,he,image_image]
    congr 1

end RealNormData
end

open Set MeasureTheory Metric

theorem equality_implies_linearHanner {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty)
    (heq : (volume K).toReal * (volume (coordinatePolar K)).toReal =
      (4 : ℝ)^n / (Nat.factorial n : ℝ)) : IsLinearHanner K := by
  obtain ⟨g,h,hg,-,hd,hmh,hmg⟩ :=
    equality_polar_gauge_medians_eq hn hK hconv hsym hint heq
  have hdim : Module.finrank ℝ g.Space = n := by simpa using g.spaceEquiv.finrank_eq
  have hpos : 0 < Module.finrank ℝ g.Space := by omega
  let : Nontrivial g.Space := Module.finrank_pos_iff.mp hpos
  have hdual : HasMetricMedians (g.Space →L[ℝ] ℝ) :=
    HasMetricMedians.linearIsometryEquiv (E:=h.Space) (F:=(g.Space →L[ℝ] ℝ))
      hmh hd.dualIsometry
  rw [← hg]
  exact (g.hannerSpace_iff_linearHanner).mp (hannerSpace_of_medians hmg hdual)

theorem symmetric_mahler_equality_oai {n : ℕ} (hn : 1 ≤ n)
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hconv : Convex ℝ K)
    (hsym : ∀ x ∈ K, -x ∈ K) (hint : (interior K).Nonempty) :
    ((volume K).toReal * (volume (coordinatePolar K)).toReal =
      (4 : ℝ)^n / (Nat.factorial n : ℝ)) ↔ IsLinearHanner K := by
  exact ⟨equality_implies_linearHanner hn hK hconv hsym hint,
    IsLinearHanner.volumeProduct⟩

end SymmetricMahler

end

end OAI
end

theorem solution : type_of% @OAI.SymmetricMahler.symmetric_mahler_equality_oai := @OAI.SymmetricMahler.symmetric_mahler_equality_oai
