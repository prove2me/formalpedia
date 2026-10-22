-- Prove2me | solution 1 for GraphonGames.Stability.proposition_3_17_unique_equilibrium
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-21T11:43:34.344312+00:00
-- url     : https://prove2.me/submissions/6aaddfea-f050-4cee-ae86-79baaef7b9e6

/-
Complete Proposition3.17: actual Nash-equilibrium existence and a.e. uniqueness.
New assembly follows Carmona, Cooney, Graves and Laurière, arXiv1911.10664v1, pp.15–16.
Accepted aggregate existence, aggregate sensitivity and best-response sensitivity proofs
are reused inline below, preserving their source and predecessor credits.
Alexander Richard Towell (queelius): direction and stewardship.
OpenAI Codex: substantial formalization, verification and documentation assistance.
This is formalization of existing mathematics, not a novelty or human-review claim.
-/
/-
Complete aggregate-profile L2 Lipschitz estimate, including the actual kernel-operator bound.
Original mathematics: René Carmona, Daniel B. Cooney, Christy V. Graves and Mathieu Laurière,
Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, Lemma 3.16, display (15).
Platform definitions and statement: mikedeng1; statement review: Shuze Chen.
Alexander Richard Towell (queelius): research direction and contribution stewardship.
OpenAI Codex: substantial formalization, verification and documentation assistance.
Lean/Mathlib contributors supply the underlying analysis and proof infrastructure.
This is a formalization of the source result, not a claim of new mathematics or human review.
-/
import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting
open MeasureTheory
open scoped ENNReal
namespace GraphonGames.Stability

lemma l2_sq {A : Type*} [MeasurableSpace A] (μ : Measure A) (f : A → ℝ) :
    eLpNorm f 2 μ ^ 2 = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂μ := by
  simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
    (eLpNorm_nnreal_pow_eq_lintegral (μ := μ) (f := f) (p := 2) (by norm_num))

lemma kernel_bound (w : I → I → ℝ) (hw : IsGraphon w) (g : I → ℝ)
    (hg : MemLp g 2 volume) :
    eLpNorm (graphonApply w g) 2 volume ≤
      eLpNorm (Function.uncurry w) 2 (volume : Measure (I × I)) * eLpNorm g 2 volume := by
  have hrow (x : I) : Measurable (w x) :=
    hw.1.comp (measurable_const.prodMk measurable_id)
  have hpoint (x : I) : ‖graphonApply w g x‖ₑ ≤
      eLpNorm (w x) 2 volume * eLpNorm g 2 volume := by
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume
      (Real.holderConjugate_iff.mpr (by norm_num : (1 : ℝ) < 2 ∧ (2 : ℝ)⁻¹ + 2⁻¹ = 1))
      (hrow x).enorm.aemeasurable hg.1.enorm
    simpa only [Pi.mul_apply, enorm_mul,
      eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ∞), ENNReal.toReal_ofNat] using h
  have hsq : eLpNorm (graphonApply w g) 2 volume ^ 2 ≤
      (eLpNorm (Function.uncurry w) 2 (volume : Measure (I × I)) * eLpNorm g 2 volume) ^ 2 := by
    rw [l2_sq]
    calc
      (∫⁻ x, ‖graphonApply w g x‖ₑ ^ 2) ≤
          ∫⁻ x, (eLpNorm (w x) 2 volume * eLpNorm g 2 volume) ^ 2 :=
        lintegral_mono fun x => ENNReal.pow_le_pow_left (hpoint x)
      _ = (∫⁻ x, ∫⁻ y, ‖w x y‖ₑ ^ 2) * eLpNorm g 2 volume ^ 2 := by
        simp_rw [mul_pow, l2_sq (volume : Measure I) (w _)]
        exact lintegral_mul_const _ (hw.1.enorm.pow_const 2).lintegral_prod_right
      _ = (eLpNorm (Function.uncurry w) 2 (volume : Measure (I × I)) *
          eLpNorm g 2 volume) ^ 2 := by
        rw [mul_pow, l2_sq (volume : Measure (I × I)) (Function.uncurry w)]
        congr 1
        exact (lintegral_prod _ (hw.1.enorm.pow_const 2).aemeasurable).symm
  apply (ENNReal.rpow_le_rpow_iff (z := 2) (by norm_num)).mp
  simpa only [ENNReal.rpow_two] using hsq

lemma graphon_memLp (w : I → I → ℝ) (hw : IsGraphon w) (g : I → ℝ)
    (hg : MemLp g 2 volume) : MemLp (graphonApply w g) 2 volume := by
  refine ⟨?_, (kernel_bound w hw g hg).trans_lt (ENNReal.mul_lt_top hw.2.2.2 hg.2)⟩
  exact (hw.1.aestronglyMeasurable.mul (hg.comp_snd (volume : Measure I)).1).integral_prod_right'

lemma opNorm_finite (w : I → I → ℝ) (hw : IsGraphon w) : opNorm w < ∞ := by
  refine lt_of_le_of_lt ?_ hw.2.2.2
  apply iSup_le
  intro g
  apply iSup_le
  intro hg
  simpa only [hg.2, mul_one] using kernel_bound w hw g hg.1


lemma apply_smul (w : I → I → ℝ) (g : I → ℝ) (c : ℝ) :
    graphonApply w (c • g) = c • graphonApply w g := by
  funext x
  simp only [graphonApply, Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (w x _ ) c, integral_const_mul]

lemma operator_bound (w : I → I → ℝ) (hw : IsGraphon w) (g : I → ℝ)
    (hg : MemLp g 2 volume) :
    eLpNorm (graphonApply w g) 2 volume ≤ opNorm w * eLpNorm g 2 volume := by
  by_cases h0 : eLpNorm g 2 volume = 0
  · simpa only [h0, mul_zero] using kernel_bound w hw g hg
  let r := (eLpNorm g 2 volume).toReal
  have hr : 0 < r := ENNReal.toReal_pos h0 hg.2.ne
  have he : ‖r⁻¹‖ₑ = (eLpNorm g 2 volume)⁻¹ := by
    rw [← ofReal_norm, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
      ENNReal.ofReal_inv_of_pos hr, ENNReal.ofReal_toReal hg.2.ne]
  have hunit : eLpNorm (r⁻¹ • g) 2 volume = 1 := by
    rw [eLpNorm_const_smul, he, ENNReal.inv_mul_cancel h0 hg.2.ne]
  have hb : eLpNorm (graphonApply w (r⁻¹ • g)) 2 volume ≤ opNorm w :=
    le_iSup_of_le (r⁻¹ • g) (le_iSup_of_le ⟨hg.const_smul _, hunit⟩ le_rfl)
  rw [apply_smul, eLpNorm_const_smul, he] at hb
  calc
    eLpNorm (graphonApply w g) 2 volume = eLpNorm g 2 volume *
        ((eLpNorm g 2 volume)⁻¹ * eLpNorm (graphonApply w g) 2 volume) := by
      rw [← mul_assoc, ENNReal.mul_inv_cancel h0 hg.2.ne, one_mul]
    _ ≤ eLpNorm g 2 volume * opNorm w := mul_le_mul_of_nonneg_left hb zero_le
    _ = _ := mul_comm _ _


lemma b_point (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (a z a' z' : ℝ) :
    |b a z - b a' z'| ≤ Real.sqrt cα * |a-a'| + Real.sqrt cz * |z-z'| := by
  have h := h1.2.2.1 a z a' z'
  have ha := Real.sq_sqrt h1.1
  have hz := Real.sq_sqrt h1.2.1
  have hsq1 : (Real.sqrt cα * |a-a'|)^2 = cα*(a-a')^2 := by
    rw [mul_pow, ha, sq_abs]
  have hsq2 : (Real.sqrt cz * |z-z'|)^2 = cz*(z-z')^2 := by
    rw [mul_pow, hz, sq_abs]
  have hn1 : 0 ≤ Real.sqrt cα * |a-a'| := by positivity
  have hn2 : 0 ≤ Real.sqrt cz * |z-z'| := by positivity
  have hab := sq_abs (b a z-b a' z')
  nlinarith [abs_nonneg (b a z-b a' z'), mul_nonneg hn1 hn2]

lemma b_lipschitz (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) :
    LipschitzWith ⟨Real.sqrt cα + Real.sqrt cz, by positivity⟩ (Function.uncurry b) := by
  apply LipschitzWith.of_dist_le_mul
  intro p q
  change |b p.1 p.2-b q.1 q.2| ≤ (Real.sqrt cα+Real.sqrt cz)*dist p q
  have ha : |p.1-q.1| ≤ dist p q := le_max_left _ _
  have hz : |p.2-q.2| ≤ dist p q := le_max_right _ _
  calc
    _ ≤ Real.sqrt cα*|p.1-q.1| + Real.sqrt cz*|p.2-q.2| := b_point b μ0 cα cz h1 _ _ _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left ha (Real.sqrt_nonneg cα),
      mul_le_mul_of_nonneg_left hz (Real.sqrt_nonneg cz)]

lemma b_memLp (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (a z : I → ℝ)
    (ha : MemLp a 2 volume) (hz : MemLp z 2 volume) :
    MemLp (fun x => b (a x) (z x)) 2 volume := by
  have hp : MemLp (fun x => (a x,z x)) 2 volume := memLp_prod_iff.mpr ⟨ha,hz⟩
  have hl : LipschitzWith ⟨Real.sqrt cα+Real.sqrt cz, by positivity⟩
      (fun p : ℝ × ℝ => b p.1 p.2-b 0 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro p q
    simpa only [dist_sub_right, Function.uncurry] using (b_lipschitz b μ0 cα cz h1).dist_le_mul p q
  have hh := hl.comp_memLp (by simp) hp
  have hc : MemLp (fun _ : I => b 0 0) 2 volume := memLp_const _
  convert hh.add hc using 1
  ext x
  simp [Function.comp_def]


lemma b_difference_bound (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (a1 a2 z1 z2 : I → ℝ)
    (ha1 : MemLp a1 2 volume) (ha2 : MemLp a2 2 volume)
    (hz1 : MemLp z1 2 volume) (hz2 : MemLp z2 2 volume) :
    eLpNorm (fun x => b (a1 x) (z1 x)-b (a2 x) (z2 x)) 2 volume ≤
      ENNReal.ofReal (Real.sqrt cα) * eLpNorm (a1-a2) 2 volume +
      ENNReal.ofReal (Real.sqrt cz) * eLpNorm (z1-z2) 2 volume := by
  let A : I → ℝ := fun x => ‖(a1-a2) x‖
  let Z : I → ℝ := fun x => ‖(z1-z2) x‖
  have ha : MemLp A 2 volume := (ha1.sub ha2).norm
  have hz : MemLp Z 2 volume := (hz1.sub hz2).norm
  calc
    _ ≤ eLpNorm (Real.sqrt cα • A + Real.sqrt cz • Z) 2 volume := by
      apply eLpNorm_mono_ae
      filter_upwards [] with x
      have hn : 0 ≤ (Real.sqrt cα • A + Real.sqrt cz • Z) x := by
        dsimp [A,Z]; positivity
      rw [Real.norm_of_nonneg hn]
      exact b_point b μ0 cα cz h1 _ _ _ _
    _ ≤ eLpNorm (Real.sqrt cα • A) 2 volume + eLpNorm (Real.sqrt cz • Z) 2 volume :=
      eLpNorm_add_le (ha.const_smul _).1 (hz.const_smul _).1 (by norm_num)
    _ = _ := by
      simp only [eLpNorm_const_smul, A, Z, eLpNorm_norm, ← ofReal_norm,
        Real.norm_of_nonneg (Real.sqrt_nonneg _)]

lemma aggregate_difference (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (w : I → I → ℝ) (hw : IsGraphon w)
    (a1 a2 z1 z2 : I → ℝ) (ha1 : MemLp a1 2 volume) (ha2 : MemLp a2 2 volume)
    (hz1 : IsAggregate w b a1 z1) (hz2 : IsAggregate w b a2 z2) :
    (z1-z2) =ᵐ[volume] graphonApply w (fun y => b (a1 y) (z1 y)-b (a2 y) (z2 y)) := by
  have hb1 := b_memLp b μ0 cα cz h1 a1 z1 ha1 hz1.1
  have hb2 := b_memLp b μ0 cα cz h1 a2 z2 ha2 hz2.1
  have hp1 := hw.2.2.integrable_mul (hb1.comp_snd (volume : Measure I))
  have hp2 := hw.2.2.integrable_mul (hb2.comp_snd (volume : Measure I))
  filter_upwards [hz1.2,hz2.2,hp1.prod_right_ae,hp2.prod_right_ae] with x hx1 hx2 hi1 hi2
  dsimp [graphonApply]
  rw [hx1,hx2]
  simp_rw [mul_sub]
  exact (integral_sub hi1 hi2).symm


end GraphonGames.Stability
open GraphonGames.Stability

theorem prior_aggregate_lipschitz
    (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (α1 α2 : I → ℝ) (hα1 : MemLp α1 2 volume)
    (hα2 : MemLp α2 2 volume)
    (z1 z2 : I → ℝ) (hz1 : IsAggregate w b α1 z1)
    (hz2 : IsAggregate w b α2 z2) :
    eLpNorm (z1-z2) 2 volume ≤
      ENNReal.ofReal (Real.sqrt cα * (opNorm w).toReal /
        (1-Real.sqrt cz * (opNorm w).toReal)) * eLpNorm (α1-α2) 2 volume := by
  have hb := (b_memLp b μ0 cα cz h1 α1 z1 hα1 hz1.1).sub
    (b_memLp b μ0 cα cz h1 α2 z2 hα2 hz2.1)
  have hd := eLpNorm_congr_ae (p := 2) (aggregate_difference b μ0 cα cz h1 w hw α1 α2 z1 z2 hα1 hα2 hz1 hz2)
  have hB := b_difference_bound b μ0 cα cz h1 α1 α2 z1 z2 hα1 hα2 hz1.1 hz2.1
  have hO := operator_bound w hw (fun y => b (α1 y) (z1 y)-b (α2 y) (z2 y)) hb
  have hm : eLpNorm (z1-z2) 2 volume ≤ opNorm w *
      (ENNReal.ofReal (Real.sqrt cα)*eLpNorm (α1-α2) 2 volume +
       ENNReal.ofReal (Real.sqrt cz)*eLpNorm (z1-z2) 2 volume) := by
    exact hd.le.trans (hO.trans (mul_le_mul_of_nonneg_left hB zero_le))
  have hA := (hα1.sub hα2).2.ne
  have hZ := (hz1.1.sub hz2.1).2.ne
  have hN := (opNorm_finite w hw).ne
  have hmreal := ENNReal.toReal_mono (by finiteness) hm
  rw [ENNReal.toReal_mul, ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _),
    ENNReal.toReal_ofReal (Real.sqrt_nonneg _)] at hmreal
  have hden : 0 < 1-Real.sqrt cz*(opNorm w).toReal := by linarith
  have hcoef : 0 ≤ Real.sqrt cα*(opNorm w).toReal /
      (1-Real.sqrt cz*(opNorm w).toReal) := by positivity
  apply (ENNReal.toReal_le_toReal hZ (by finiteness)).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hcoef]
  rw [div_mul_eq_mul_div, le_div_iff₀ hden]
  nlinarith

#print axioms GraphonGames.Stability.kernel_bound
#print axioms GraphonGames.Stability.graphon_memLp
#print axioms GraphonGames.Stability.opNorm_finite
#print axioms GraphonGames.Stability.operator_bound
#print axioms GraphonGames.Stability.b_point
#print axioms GraphonGames.Stability.b_lipschitz
#print axioms GraphonGames.Stability.b_memLp
#print axioms GraphonGames.Stability.b_difference_bound
#print axioms GraphonGames.Stability.aggregate_difference
#print axioms prior_aggregate_lipschitz

set_option autoImplicit false
namespace GraphonGames.Stability
lemma graphon_sub_ae (w : I → I → ℝ) (hw : IsGraphon w) (g h : I → ℝ)
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) :
    (graphonApply w g - graphonApply w h) =ᵐ[volume] graphonApply w (g-h) := by
  have hp1 := hw.2.2.integrable_mul (hg.comp_snd (volume : Measure I))
  have hp2 := hw.2.2.integrable_mul (hh.comp_snd (volume : Measure I))
  filter_upwards [hp1.prod_right_ae,hp2.prod_right_ae] with x hi1 hi2
  change (∫ y, w x y*g y) - (∫ y,w x y*h y) = ∫ y,w x y*(g y-h y)
  simp_rw [mul_sub]
  exact (integral_sub hi1 hi2).symm

lemma aggregate_map_bound (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz) (w : I → I → ℝ) (hw : IsGraphon w)
    (α z z' : I → ℝ) (hα : MemLp α 2 volume) (hz : MemLp z 2 volume) (hz' : MemLp z' 2 volume) :
    eLpNorm (graphonApply w (fun y => b (α y) (z y)) -
      graphonApply w (fun y => b (α y) (z' y))) 2 volume ≤
      (opNorm w * ENNReal.ofReal (Real.sqrt cz)) * eLpNorm (z-z') 2 volume := by
  have hb := b_memLp b μ0 cα cz h1 α z hα hz
  have hb' := b_memLp b μ0 cα cz h1 α z' hα hz'
  rw [eLpNorm_congr_ae (graphon_sub_ae w hw _ _ hb hb')]
  have h := b_difference_bound b μ0 cα cz h1 α α z z' hα hα hz hz'
  simp only [sub_self,eLpNorm_zero,mul_zero,zero_add] at h
  exact (operator_bound w hw _ (hb.sub hb')).trans
    (by simpa only [mul_assoc,Pi.sub_def] using mul_le_mul_of_nonneg_left h (show 0 ≤ opNorm w from zero_le))
end GraphonGames.Stability

theorem prior_aggregate_exists_unique
    (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (α : I → ℝ) (hα : MemLp α 2 volume) :
    ∃ z, IsAggregate w b α z ∧
      ∀ z', IsAggregate w b α z' → z' =ᵐ[volume] z := by
  let F : Lp ℝ 2 (volume : Measure I) → Lp ℝ 2 (volume : Measure I) := fun z =>
    (graphon_memLp w hw _ (b_memLp b μ0 cα cz h1 α z hα (Lp.memLp z))).toLp
      (graphonApply w (fun y => b (α y) (z y)))
  let K : NNReal := ⟨Real.sqrt cz*(opNorm w).toReal,by positivity⟩
  have hK : (K:ℝ≥0∞) = opNorm w*ENNReal.ofReal (Real.sqrt cz) := by
    calc
      (K:ℝ≥0∞) = ENNReal.ofReal (K:ℝ) := ENNReal.ofReal_coe_nnreal.symm
      _ = _ := by
        change ENNReal.ofReal (Real.sqrt cz*(opNorm w).toReal) = _
        rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _), ENNReal.ofReal_toReal (opNorm_finite w hw).ne]
        exact mul_comm _ _
  have hF : ContractingWith K F := by
    refine ⟨hW,?_⟩
    intro z z'
    dsimp only [F]
    rw [Lp.edist_toLp_toLp,Lp.edist_def,hK]
    exact aggregate_map_bound b μ0 cα cz h1 w hw α z z' hα (Lp.memLp z) (Lp.memLp z')
  let z := hF.fixedPoint F
  have hzfix : F z=z := hF.fixedPoint_isFixedPt
  have hz : IsAggregate w b α z := by
    refine ⟨Lp.memLp z,?_⟩
    have he : (F z : I → ℝ) =ᵐ[volume] graphonApply w (fun y => b (α y) (z y)) :=
      MemLp.coeFn_toLp _
    rw [hzfix] at he
    exact he
  refine ⟨z,hz,?_⟩
  intro z' hz'
  have h := prior_aggregate_lipschitz b μ0 cα cz h1 w hw hW α α hα hα z' z hz' hz
  simp only [sub_self,eLpNorm_zero,mul_zero] at h
  have he := (eLpNorm_eq_zero_iff (hz'.1.sub hz.1).1 (by norm_num : (2:ℝ≥0∞)≠0)).mp
    (le_antisymm h zero_le)
  filter_upwards [he] with x hx
  exact sub_eq_zero.mp hx

#print axioms prior_aggregate_exists_unique

/-
Complete best-response sensitivity and L2 bound from the actual Assumption4.
Original mathematics: Carmona, Cooney, Graves and Laurière, Stochastic Graphon Games I,
arXiv:1911.10664v1, Lemma3.7; their source credits Parise and Ozdaglar [26].
Platform definitions/statements: mikedeng1; review: Shuze Chen.
Alexander Richard Towell (queelius) directed this formalization; OpenAI Codex substantially
assisted proof development, verification and documentation using Lean/Mathlib.
No claim of mathematical novelty or independent human review is made.
-/
open MeasureTheory
open scoped ENNReal
namespace BestResponseResearch
open GraphonGames.Existence
variable {J : ℝ → ℝ → ℝ} {ℓc ℓJ : ℝ} (h4 : Asm4 J ℓc ℓJ)
include h4
lemma strongly_convex (z : ℝ) : StrongConvexOn Set.univ ℓc (fun a => J a z) := by
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb u v hu hv huv
  have hv' : v = 1-u := by linarith
  have h := h4.2.2.2.1 a b z u hu (by linarith)
  simp only [smul_eq_mul, Real.norm_eq_abs]
  rw [hv']
  convert h using 1 <;> ring
lemma differentiable (z : ℝ) : Differentiable ℝ (fun a => J a z) :=
  (h4.2.2.1 z).differentiable (by norm_num)
lemma convex (z : ℝ) : ConvexOn ℝ Set.univ (fun a => J a z) :=
  ((strongly_convex h4 z).strictConvexOn h4.1).convexOn
lemma derivative_growth (z a b : ℝ) (hab : a ≤ b) :
    ℓc*(b-a) ≤ deriv (fun x => J x z) b - deriv (fun x => J x z) a := by
  let g : ℝ → ℝ := fun x => J x z - ℓc/2*x^2
  have hg : ConvexOn ℝ Set.univ g := by
    simpa only [Real.norm_eq_abs, sq_abs] using strongConvexOn_iff_convex.mp (strongly_convex h4 z)
  have hd (x : ℝ) : HasDerivAt g (deriv (fun x => J x z) x - ℓc*x) x := by
    have hq : HasDerivAt (fun y : ℝ => ℓc/2*y^2) (ℓc*x) x := by
      convert ((hasDerivAt_id x).pow 2).const_mul (ℓc/2) using 1 <;> norm_num <;> first | rfl | ring
    exact ((differentiable h4 z x).hasDerivAt).sub hq
  have hm := hg.monotoneOn_deriv (fun x _ => (hd x).differentiableAt)
  have hh := hm (Set.mem_univ a) (Set.mem_univ b) hab
  rw [(hd a).deriv, (hd b).deriv] at hh
  linarith
lemma exists_minimizer (z : ℝ) : ∃ a, ∀ b, J a z ≤ J b z := by
  let d := deriv (fun a => J a z) 0
  let R := (|d|+1)/ℓc
  have hc := h4.1
  have hR : 0 < R := div_pos (by positivity) hc
  have hRc : ℓc*R = |d|+1 := by dsimp [R]; field_simp
  have hlo := derivative_growth h4 z (-R) 0 (by linarith)
  have hhi := derivative_growth h4 z 0 R hR.le
  have hl : deriv (fun a => J a z) (-R) ≤ 0 := by
    have hab := le_abs_self d
    change d - deriv (fun a => J a z) (-R) ≥ ℓc * (0- -R) at hlo
    nlinarith
  have hu : 0 ≤ deriv (fun a => J a z) R := by
    have hab := neg_abs_le d
    change ℓc*(R-0) ≤ deriv (fun a => J a z) R-d at hhi
    nlinarith
  obtain ⟨a, _, ha⟩ := intermediate_value_Icc (show -R ≤ R by linarith)
    ((h4.2.2.1 z).continuous_deriv (by norm_num)).continuousOn (show (0:ℝ) ∈ Set.Icc _ _ from ⟨hl,hu⟩)
  refine ⟨a, fun b => ?_⟩
  rcases lt_trichotomy a b with hab | rfl | hba
  · have h := (convex h4 z).deriv_le_slope (Set.mem_univ a) (Set.mem_univ b) hab (differentiable h4 z a)
    rw [ha, slope_def_field] at h
    have hh := (le_div_iff₀ (sub_pos.mpr hab)).mp h
    linarith
  · rfl
  · have h := (convex h4 z).slope_le_deriv (Set.mem_univ b) (Set.mem_univ a) hba (differentiable h4 z a)
    rw [ha, slope_def_field] at h
    have hh := (div_le_iff₀ (sub_pos.mpr hba)).mp h
    linarith
noncomputable def response (J : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  Classical.epsilon (fun a => ∀ b, J a z ≤ J b z)
lemma response_min (z b : ℝ) : J (response J z) z ≤ J b z :=
  Classical.epsilon_spec (exists_minimizer h4 z) b
lemma response_deriv (z : ℝ) : deriv (fun a => J a z) (response J z) = 0 := by
  have hm : IsMinOn (fun a => J a z) Set.univ (response J z) := fun b _ => response_min h4 z b
  exact (hm.isLocalMin (by simp)).deriv_eq_zero
lemma response_bound (z z' : ℝ) : |response J z-response J z'| ≤ (ℓJ/ℓc)*|z-z'| := by
  have hc := h4.1
  have hder := h4.2.2.2.2 (response J z') z z'
  rw [response_deriv h4 z'] at hder
  rw [zero_sub, abs_neg, abs_sub_comm z' z] at hder
  rcases le_total (response J z) (response J z') with h | h
  · have hg := derivative_growth h4 z (response J z) (response J z') h
    rw [response_deriv h4 z, sub_zero] at hg
    have hb := (le_abs_self (deriv (fun a => J a z) (response J z'))).trans hder
    rw [abs_of_nonpos (sub_nonpos.mpr h)]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith [hg.trans hb]
  · have hg := derivative_growth h4 z (response J z') (response J z) h
    rw [response_deriv h4 z, zero_sub] at hg
    have hb := (neg_le_abs (deriv (fun a => J a z) (response J z'))).trans hder
    rw [abs_of_nonneg (sub_nonneg.mpr h)]
    have hh := hg.trans hb
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hc).mpr
    nlinarith
lemma response_unique (z a : ℝ) (ha : ∀ b, J a z ≤ J b z) : a = response J z := by
  exact ((strongly_convex h4 z).strictConvexOn h4.1).eq_of_isMinOn
    (fun b _ => ha b) (fun b _ => response_min h4 z b) (Set.mem_univ a) (Set.mem_univ _)
lemma response_lipschitz : LipschitzWith ⟨ℓJ/ℓc, div_nonneg h4.2.1 h4.1.le⟩ (response J) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  change |response J x-response J y| ≤ (ℓJ/ℓc)*|x-y|
  exact response_bound h4 x y
lemma profile_memLp (z : unitInterval → ℝ) (hz : MemLp z 2 volume) :
    MemLp (GraphonGames.Stability.bestResponse J z) 2 volume := by
  have hg : LipschitzWith ⟨ℓJ/ℓc, div_nonneg h4.2.1 h4.1.le⟩ (fun x => response J x-response J 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa only [dist_sub_right] using (response_lipschitz h4).dist_le_mul x y
  have hm := hg.comp_memLp (by simp) hz
  have hc : MemLp (fun _ : unitInterval => response J 0) 2 volume := memLp_const _
  convert hm.add hc using 1
  ext x
  simp [Function.comp_def, GraphonGames.Stability.bestResponse, response]
end BestResponseResearch
open GraphonGames.Stability

theorem prior_best_response_lipschitz
    (J : ℝ → ℝ → ℝ) (ℓc ℓJ : ℝ) (h4 : GraphonGames.Existence.Asm4 J ℓc ℓJ)
    (z1 z2 : I → ℝ) (hz1 : MemLp z1 2 volume)
    (hz2 : MemLp z2 2 volume) :
    eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume ≤
      ENNReal.ofReal (ℓJ / ℓc) * eLpNorm (z1 - z2) 2 volume := by
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
  apply Filter.Eventually.of_forall
  intro x
  simpa only [Pi.sub_apply, Real.norm_eq_abs, bestResponse, BestResponseResearch.response]
    using BestResponseResearch.response_bound h4 (z1 x) (z2 x)
#print axioms prior_best_response_lipschitz

set_option autoImplicit false

theorem solution
    (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (μ0 : Measure ℝ) (cα cz ℓc ℓJ : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (h4 : GraphonGames.Existence.Asm4 (GraphonGames.Existence.cost b f μ0) ℓc ℓJ)
    (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (h17 : ℓJ / ℓc *
      (Real.sqrt cα * (opNorm w).toReal /
        (1 - Real.sqrt cz * (opNorm w).toReal)) < 1) :
    ∃ α, IsNash w b f μ0 α ∧
      ∀ α', IsNash w b f μ0 α' → α' =ᵐ[volume] α := by
  let J := GraphonGames.Existence.cost b f μ0
  let A := Real.sqrt cα * (opNorm w).toReal / (1 - Real.sqrt cz * (opNorm w).toReal)
  have hA : 0 ≤ A := by dsimp [A]; exact div_nonneg (by positivity) (by linarith)
  have hB : 0 ≤ ℓJ/ℓc := div_nonneg h4.2.1 h4.1.le
  let K : NNReal := ⟨ℓJ/ℓc*A, mul_nonneg hB hA⟩
  have hK : (K:ℝ≥0∞) = ENNReal.ofReal (ℓJ/ℓc)*ENNReal.ofReal A := by
    rw [← ENNReal.ofReal_coe_nnreal]
    exact ENNReal.ofReal_mul hB
  let Z : Lp ℝ 2 (volume : Measure I) → I → ℝ := fun a =>
    (prior_aggregate_exists_unique b μ0 cα cz h1 w hw hW a (Lp.memLp a)).choose
  have hZ (a : Lp ℝ 2 (volume : Measure I)) : IsAggregate w b a (Z a) :=
    (prior_aggregate_exists_unique b μ0 cα cz h1 w hw hW a (Lp.memLp a)).choose_spec.1
  let F : Lp ℝ 2 (volume : Measure I) → Lp ℝ 2 (volume : Measure I) := fun a =>
    (BestResponseResearch.profile_memLp h4 (Z a) (hZ a).1).toLp (bestResponse J (Z a))
  have hbound (a a' z z' : I → ℝ) (ha : MemLp a 2 volume) (ha' : MemLp a' 2 volume)
      (hz : IsAggregate w b a z) (hz' : IsAggregate w b a' z') :
      eLpNorm (bestResponse J z-bestResponse J z') 2 volume ≤
        (K:ℝ≥0∞)*eLpNorm (a-a') 2 volume := by
    have hresp := prior_best_response_lipschitz J ℓc ℓJ h4 z z' hz.1 hz'.1
    have hagg := prior_aggregate_lipschitz b μ0 cα cz h1 w hw hW a a' ha ha' z z' hz hz'
    rw [hK,mul_assoc]
    exact hresp.trans (mul_le_mul_of_nonneg_left hagg zero_le)
  have hF : ContractingWith K F := by
    refine ⟨h17, ?_⟩
    intro a a'
    dsimp only [F]
    rw [Lp.edist_toLp_toLp,Lp.edist_def]
    exact hbound a a' (Z a) (Z a') (Lp.memLp a) (Lp.memLp a') (hZ a) (hZ a')
  let a := hF.fixedPoint F
  have hafix : F a=a := hF.fixedPoint_isFixedPt
  have hae : (a : I → ℝ) =ᵐ[volume] bestResponse J (Z a) := by
    have he : (F a : I → ℝ) =ᵐ[volume] bestResponse J (Z a) := MemLp.coeFn_toLp _
    rwa [hafix] at he
  have hN : IsNash w b f μ0 a := by
    refine ⟨Lp.memLp a, Z a, hZ a, ?_⟩
    filter_upwards [hae] with x hx
    intro β
    rw [hx]
    exact BestResponseResearch.response_min h4 (Z a x) β
  refine ⟨a,hN,?_⟩
  intro a' ha'
  obtain ⟨haLp,z',hz',hmin⟩ := ha'
  have hae' : a' =ᵐ[volume] bestResponse J z' := by
    filter_upwards [hmin] with x hx
    exact BestResponseResearch.response_unique h4 (z' x) (a' x) hx
  have hd : (a' - (a : I → ℝ)) =ᵐ[volume] bestResponse J z' - bestResponse J (Z a) := by
    filter_upwards [hae',hae] with x hx' hx
    simp only [Pi.sub_apply,hx',hx]
  have hh := hbound a' a z' (Z a) haLp (Lp.memLp a) hz' (hZ a)
  rw [← eLpNorm_congr_ae hd] at hh
  have hfin := (haLp.sub (Lp.memLp a)).2.ne
  have hhR := ENNReal.toReal_mono (by finiteness) hh
  rw [ENNReal.toReal_mul,ENNReal.coe_toReal] at hhR
  have hzero : (eLpNorm (a' - (a : I → ℝ)) 2 volume).toReal=0 := by
    have hnon := ENNReal.toReal_nonneg (a := eLpNorm (a' - (a : I → ℝ)) 2 volume)
    change _ ≤ (ℓJ/ℓc*A)*_ at hhR
    change ℓJ/ℓc*A < 1 at h17
    nlinarith
  have hezero : eLpNorm (a' - (a : I → ℝ)) 2 volume=0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right hfin
  have he := (eLpNorm_eq_zero_iff (haLp.sub (Lp.memLp a)).1 (by norm_num : (2:ℝ≥0∞)≠0)).mp hezero
  filter_upwards [he] with x hx
  exact sub_eq_zero.mp hx

#print axioms solution
