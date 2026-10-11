-- Prove2me | solution 1 for HunterPDE.Regularity.interior_H2_regularity
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-11T00:23:05.067034+00:00
-- url     : https://prove2.me/submissions/fcca92bd-0710-45e1-8717-932d87045928

import Mathlib
import Definitions.Def_HunterPDE_Regularity_WeakSolution
import Definitions.Def_HunterPDE_Regularity_DiffQuotient

open MeasureTheory
open scoped ENNReal

-- BEGIN COMPLETE MODULE H1Data
section

open MeasureTheory
namespace HunterPDE.Regularity.Proof

structure H1Data {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) where
  grad : Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  self_memLp : MemLp u 2 (volume.restrict Ω)
  weak : ∀i, Shared.HasWeakDeriv Ω (Pi.single i 1) u (grad i)
  grad_memLp : ∀i, MemLp (grad i) 2 (volume.restrict Ω)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H1Data

-- BEGIN COMPLETE MODULE MultiIndexBasics
section

namespace HunterPDE.Regularity.Proof
open HunterPDE.Shared

lemma multiIndexList_zero (n : ℕ) : multiIndexList (0 : Fin n → ℕ)=[] := by
  simp [multiIndexList]

lemma multiDeriv_zero {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    multiDeriv f 0=f := by simp [multiDeriv,multiIndexList_zero,iteratedPartial]

lemma flatMap_single_indicator {ι : Type*} [DecidableEq ι] (l : List ι) (hl : l.Nodup)
    (i : ι) (hi : i∈l) : l.flatMap (fun j => if j=i then [j] else [])=[i] := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    have hn := List.nodup_cons.mp hl
    by_cases hji : j=i
    · subst j
      have he : l.flatMap (fun j => if j=i then [j] else [])=[] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro j hj
        have hji : j≠i := by intro h; subst j; exact hn.1 hj
        simp only [if_neg hji]
      simp [he]
    · have hil : i∈l := (List.mem_cons.mp hi).resolve_left (Ne.symm hji)
      simpa [hji] using ih hn.2 hil

lemma multiIndexList_single {n : ℕ} (i : Fin n) :
    multiIndexList (Pi.single i 1)=[i] := by
  unfold multiIndexList
  have he (j : Fin n) : List.replicate ((Pi.single i 1 : Fin n → ℕ) j) j =
      if j=i then [j] else [] := by
    by_cases hj : j=i
    · subst j; simp
    · simp [hj]
  simp_rw [he]
  exact flatMap_single_indicator _ (List.nodup_finRange n) i (List.mem_finRange i)

lemma multiDeriv_single {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (i : Fin n) :
    multiDeriv f (Pi.single i 1)=partialDeriv f i := by
  simp [multiDeriv,multiIndexList_single,iteratedPartial]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE MultiIndexBasics

-- BEGIN COMPLETE MODULE WeakTestIntegral
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma test_mul_integrable {f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : LocallyIntegrableOn f Ω volume) (hφ : Shared.IsTestFunction Ω φ) :
    Integrable (fun x => f x*φ x) volume := by
  apply (integrableOn_iff_integrable_of_support_subset
    (show Function.support (fun x => f x*φ x) ⊆ tsupport φ from fun x hx =>
      subset_tsupport φ ((mul_ne_zero_iff.mp hx).2))).mp
  exact (hf.integrableOn_compact_subset hφ.2.2 hφ.2.1).mul_continuousOn
    hφ.1.continuous.continuousOn hφ.2.1

lemma test_integral_eq {f φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Shared.IsTestFunction Ω φ) :
    (∫x in Ω, f x*φ x) = ∫x, f x*φ x := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hp : φ x=0 := by
    by_contra hh
    exact hx (hφ.2.2 (subset_tsupport φ hh))
  simp only [hp,mul_zero]

lemma weakDeriv_unique (hΩ : IsOpen Ω) {α : Fin n → ℕ}
    {f g h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Shared.HasWeakDeriv Ω α f g) (hh : Shared.HasWeakDeriv Ω α f h) :
    g =ᵐ[volume.restrict Ω] h := by
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero (hg.2.1.sub hh.2.1) ?_
  · change ∀ᵐ x ∂(volume.restrict Ω), g x=h x
    rw [ae_restrict_iff' hΩ.measurableSet]
    filter_upwards [hz] with x hx hmem
    exact sub_eq_zero.mp (hx hmem)
  · intro φ hφ hc hs
    have ht : Shared.IsTestFunction Ω φ := ⟨hφ,hc,hs⟩
    have hi := (hg.2.2 φ ht).trans (hh.2.2 φ ht).symm
    rw [test_integral_eq ht,test_integral_eq ht] at hi
    simp only [smul_eq_mul,Pi.sub_apply]
    have he : (fun x => φ x*(g x-h x))=(fun x => g x*φ x-h x*φ x) := by
      funext x; ring
    rw [he,integral_sub (test_mul_integrable hg.2.1 ht) (test_mul_integrable hh.2.1 ht),hi,sub_self]

lemma chosen_weakDeriv_spec {α : Fin n → ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Shared.HasWeakDeriv Ω α f g) :
    Shared.HasWeakDeriv Ω α f (Shared.weakDeriv Ω α f) := by
  rw [Shared.weakDeriv,dif_pos (show ∃g,Shared.HasWeakDeriv Ω α f g from ⟨g,hg⟩)]
  exact Classical.choose_spec _

lemma chosen_weakDeriv_ae (hΩ : IsOpen Ω) {α : Fin n → ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hg : Shared.HasWeakDeriv Ω α f g) :
    Shared.weakDeriv Ω α f =ᵐ[volume.restrict Ω] g :=
  weakDeriv_unique hΩ (chosen_weakDeriv_spec hg) hg

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakTestIntegral

-- BEGIN COMPLETE MODULE WeakZero
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma weak_zero_self {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : LocallyIntegrableOn u Ω volume) : Shared.HasWeakDeriv Ω 0 u u := by
  refine ⟨hu,hu,?_⟩
  intro φ _
  simp only [multiDeriv_zero,Pi.zero_apply,Finset.sum_const_zero,pow_zero,one_mul]

lemma memLp_locally {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) : LocallyIntegrableOn u Ω volume :=
  locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num))

lemma weak_zero_ae (hΩ : IsOpen Ω) {u g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hg : Shared.HasWeakDeriv Ω 0 u g) : g =ᵐ[volume.restrict Ω] u :=
  weakDeriv_unique hΩ hg (weak_zero_self hg.1)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakZero

-- BEGIN COMPLETE MODULE H1Native
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma multi_mem_iff (k : ℕ) (α : Fin n → ℕ) : α∈multiIndicesLe n k ↔ ∑i,α i≤k := by
  classical
  simp only [multiIndicesLe,Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_,h⟩
    simp only [Fintype.mem_piFinset,Finset.mem_range]
    intro i
    have hi := Finset.single_le_sum (fun j _ => Nat.zero_le (α j)) (Finset.mem_univ i)
    omega

lemma order_one_cases {α : Fin n → ℕ} (h : ∑i,α i≤1) : α=0 ∨ ∃i,α=Pi.single i 1 := by
  classical
  by_cases hz : α=0
  · exact Or.inl hz
  · right
    obtain ⟨i,hi⟩ : ∃i,α i≠0 := by simpa only [funext_iff,Pi.zero_apply,not_forall] using hz
    have hsum := Finset.sum_le_one_iff.mp h
    refine ⟨i,funext (fun j => ?_)⟩
    by_cases hj : j=i
    · subst j
      simpa using (hsum i i (Finset.mem_univ _) (Finset.mem_univ _) hi hi).2
    · have hzj : α j=0 := by
        by_contra hh
        exact hj (hsum j i (Finset.mem_univ _) (Finset.mem_univ _) hh hi).1
      simp [hzj,hj]

lemma H1Data.memW {u : EuclideanSpace ℝ (Fin n) → ℝ} (H : H1Data Ω u) : MemW 1 2 Ω u := by
  intro α hα
  rcases order_one_cases ((multi_mem_iff 1 α).mp hα) with rfl | ⟨i,rfl⟩
  · exact ⟨u,weak_zero_self (memLp_locally H.self_memLp),H.self_memLp⟩
  · exact ⟨H.grad i,H.weak i,H.grad_memLp i⟩

lemma h1Data_exists (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemW 1 2 Ω u) : Nonempty (H1Data Ω u) := by
  classical
  obtain ⟨v,hv,hvLp⟩ := hu 0 ((multi_mem_iff 1 0).mpr (by simp))
  have huLp : MemLp u 2 (volume.restrict Ω) := hvLp.ae_eq (weak_zero_ae hΩ hv)
  have hg (i : Fin n) := hu (Pi.single i 1) ((multi_mem_iff 1 _).mpr (by simp))
  choose g hweak hLp using hg
  exact ⟨⟨g,huLp,hweak,hLp⟩⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H1Native

-- BEGIN COMPLETE MODULE WeakSolutionWitness
section

open MeasureTheory Set

namespace HunterPDE.Regularity.Proof

theorem weak_solution_witness_identity {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    {a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    {f u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hsol : IsWeakSolution Ω a f u) (U : H1Data Ω u) (V : H1Data Ω v)
    (hv : MemW0 1 2 Ω v) :
    (∑ i, ∑ j, ∫ x in Ω, a i j x * U.grad i x * V.grad j x) =
      ∫ x in Ω, f x * v x := by
  rw [← hsol.2 v hv]
  unfold bilinForm
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [chosen_weakDeriv_ae hΩ (U.weak i),
    chosen_weakDeriv_ae hΩ (V.weak j)] with x hi hj
  rw [hi, hj]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakSolutionWitness

-- BEGIN COMPLETE MODULE L2Energy
section

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity.Proof

noncomputable def l2Norm {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) : ℝ :=
  (eLpNorm f 2 μ).toReal

lemma l2Norm_nonneg {E : Type*} [MeasurableSpace E] (μ : Measure E) (f : E → ℝ) :
    0 ≤ l2Norm μ f := ENNReal.toReal_nonneg

lemma integral_mul_eq_inner_toLp {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ∫ x, f x * g x ∂μ = inner ℝ (hf.toLp f) (hg.toLp g) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with x hfx hgx
  simp only [RCLike.inner_apply, hfx, hgx, starRingEnd_apply, star_trivial]
  ring

lemma abs_integral_mul_le_l2 {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤ l2Norm μ f * l2Norm μ g := by
  rw [integral_mul_eq_inner_toLp hf hg]
  simpa only [Real.norm_eq_abs, Lp.norm_toLp, l2Norm] using
    norm_inner_le_norm (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)

lemma integral_sq_eq_l2_sq {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f : E → ℝ} (hf : MemLp f 2 μ) :
    ∫ x, f x ^ 2 ∂μ = l2Norm μ f ^ 2 := by
  simp_rw [pow_two]
  rw [integral_mul_eq_inner_toLp hf hf, real_inner_self_eq_norm_sq,
    Lp.norm_toLp]
  simp only [l2Norm, pow_two]

lemma l2Norm_add_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    l2Norm μ (f + g) ≤ l2Norm μ f + l2Norm μ g := by
  change (eLpNorm (f + g) 2 μ).toReal ≤ (eLpNorm f 2 μ).toReal + (eLpNorm g 2 μ).toReal
  rw [← Lp.norm_toLp _ (hf.add hg), MemLp.toLp_add, ← Lp.norm_toLp _ hf, ← Lp.norm_toLp _ hg]
  exact norm_add_le _ _

lemma energy_absorption {θ B X Y : ℝ} (hθ : 0 < θ) (hB : 0 ≤ B)
    (_hX : 0 ≤ X) (hY : 0 ≤ Y) (h : θ * X ^ 2 ≤ B * Y * X + B * Y ^ 2) :
    X ≤ (2 * B / θ + 1) * Y := by
  by_contra hn
  have hh : (2 * B / θ + 1) * Y < X := lt_of_not_ge hn
  have hk : 0 ≤ 2 * B / θ := div_nonneg (by positivity) hθ.le
  have hYX : Y < X := lt_of_le_of_lt (by nlinarith [mul_nonneg hk hY]) hh
  have hXp : 0 < X := lt_of_le_of_lt hY hYX
  have hYY : B * Y ^ 2 ≤ B * Y * X := by
    nlinarith [mul_nonneg (mul_nonneg hB hY) (sub_nonneg.mpr hYX.le)]
  have hsmall : θ * X ≤ 2 * B * Y := by
    by_contra hh
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hh)) hXp
    nlinarith
  have hlarge := mul_lt_mul_of_pos_left hh hθ
  have hc : θ * (2 * B / θ + 1) = 2 * B + θ := by field_simp
  rw [← mul_assoc, hc] at hlarge
  nlinarith [mul_nonneg hθ.le hY]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE L2Energy

-- BEGIN COMPLETE MODULE EllipticEnergy
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem elliptic_integral_bound {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {n : ℕ} (a : Fin n → Fin n → E → ℝ) (g : Fin n → E → ℝ)
    (hg : ∀ i, MemLp (g i) 2 μ) (θ : ℝ)
    (ha : ∀ i j, Integrable (fun x => a i j x * g i x * g j x) μ)
    (hell : ∀ᵐ x ∂μ, θ * ∑ i, g i x ^ 2 ≤ ∑ i, ∑ j, a i j x * g i x * g j x) :
    θ * ∑ i, l2Norm μ (g i) ^ 2 ≤ ∑ i, ∑ j, ∫ x, a i j x * g i x * g j x ∂μ := by
  have hi (i : Fin n) : Integrable (fun x => g i x ^ 2) μ := by
    have hh : Integrable (fun x => g i x * g i x) μ := (hg i).integrable_mul (hg i)
    simpa only [pow_two] using hh
  have hleft : Integrable (fun x => θ * ∑ i, g i x ^ 2) μ :=
    (integrable_finsetSum _ (fun i _ => hi i)).const_mul θ
  have hright : Integrable (fun x => ∑ i, ∑ j, a i j x * g i x * g j x) μ :=
    integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => ha i j))
  have hh := integral_mono_ae hleft hright hell
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at hh
  simp_rw [integral_sq_eq_l2_sq (hg _)] at hh
  rw [integral_finsetSum _ (fun i _ =>
    integrable_finsetSum _ (fun j _ => ha i j))] at hh
  simp_rw [integral_finsetSum _ (fun j _ => ha _ j)] at hh
  exact hh

theorem coefficient_product_integrable {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {a f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (ha : AEStronglyMeasurable a μ) (M : ℝ) (hM : ∀ᵐ x ∂μ, |a x| ≤ M) :
    Integrable (fun x => a x * f x * g x) μ := by
  have hi := (hf.integrable_mul hg).bdd_mul ha (by simpa only [Real.norm_eq_abs] using hM)
  simpa only [Pi.mul_apply, mul_assoc] using hi

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE EllipticEnergy

-- BEGIN COMPLETE MODULE CutoffEnergyIdentity
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem cutoff_bilinear_identity {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {n : ℕ} (a : Fin n → Fin n → E → ℝ) (g d : Fin n → E → ℝ)
    (η u : E → ℝ)
    (hmain : ∀ i j, Integrable (fun x => a i j x * (η x * g i x) * (η x * g j x)) μ)
    (hcross : ∀ i j, Integrable (fun x => (η x * g i x) * (a i j x * d j x * u x)) μ) :
    (∑ i, ∑ j, ∫ x, a i j x * g i x * (η x ^ 2 * g j x + 2 * η x * d j x * u x) ∂μ) =
      (∑ i, ∑ j, ∫ x, a i j x * (η x * g i x) * (η x * g j x) ∂μ) +
      2 * ∑ i, ∑ j, ∫ x, (η x * g i x) * (a i j x * d j x * u x) ∂μ := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← integral_const_mul, ← integral_add (hmain i j) ((hcross i j).const_mul 2)]
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem energy_bound_two_inputs {θ K X F U : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hX : 0 ≤ X) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (h : θ * X ^ 2 ≤ F * U + K * U * X) :
    X ≤ (2 * (1 + K) / θ + 1) * (F + U) := by
  apply energy_absorption hθ (by positivity) hX (by positivity)
  have h1 : F * U ≤ (1 + K) * (F + U) ^ 2 := by
    nlinarith [sq_nonneg F, sq_nonneg U, mul_nonneg hF hU,
      mul_nonneg hK (sq_nonneg (F + U))]
  have h2 : K * U * X ≤ (1 + K) * (F + U) * X := by
    nlinarith [mul_nonneg hK hF, mul_nonneg hF hX,
      mul_nonneg hU hX, mul_nonneg (mul_nonneg hK hF) hX]
  linarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CutoffEnergyIdentity

-- BEGIN COMPLETE MODULE FiniteEnergyNorm
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

noncomputable def gradientL2 {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) (g : Fin n → E → ℝ) : ℝ :=
  Real.sqrt (∑ i, l2Norm μ (g i) ^ 2)

lemma gradientL2_nonneg {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) (g : Fin n → E → ℝ) : 0 ≤ gradientL2 μ g := Real.sqrt_nonneg _

lemma gradientL2_sq {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) (g : Fin n → E → ℝ) :
    gradientL2 μ g ^ 2 = ∑ i, l2Norm μ (g i) ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))

lemma l2Norm_le_gradientL2 {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) (g : Fin n → E → ℝ) (i : Fin n) :
    l2Norm μ (g i) ≤ gradientL2 μ g := by
  have h := Finset.single_le_sum (fun j _ => sq_nonneg (l2Norm μ (g j))) (Finset.mem_univ i)
  rw [← gradientL2_sq] at h
  nlinarith [l2Norm_nonneg μ (g i), gradientL2_nonneg μ g]

lemma sum_l2Norm_le_gradientL2 {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure E) (g : Fin n → E → ℝ) :
    ∑ i, l2Norm μ (g i) ≤ n * gradientL2 μ g := by
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => l2Norm_le_gradientL2 μ g i)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE FiniteEnergyNorm

-- BEGIN COMPLETE MODULE L2Bounds
section

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity.Proof

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {f g : E → ℝ}

lemma l2Norm_mono (hg : MemLp g 2 μ) (h : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖g x‖) :
    l2Norm μ f ≤ l2Norm μ g :=
  ENNReal.toReal_mono hg.2.ne (eLpNorm_mono_ae h)

lemma l2Norm_const_mul (c : ℝ) (hf : MemLp f 2 μ) :
    l2Norm μ (fun x => c * f x) = |c| * l2Norm μ f := by
  change (eLpNorm (c • f) 2 μ).toReal = _
  rw [← Lp.norm_toLp _ (hf.const_smul c), MemLp.toLp_const_smul c hf, norm_smul,
    Real.norm_eq_abs, Lp.norm_toLp]
  rfl

lemma memLp_mul_of_bound (hf : MemLp f 2 μ) (hg : AEStronglyMeasurable g μ)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ᵐ x ∂μ, |g x| ≤ M) :
    MemLp (fun x => g x * f x) 2 μ := by
  apply (hf.const_smul M).mono (hg.mul hf.1)
  filter_upwards [hbound] with x hx
  simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
  exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

lemma l2Norm_mul_le (hf : MemLp f 2 μ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂μ, |g x| ≤ M) :
    l2Norm μ (fun x => g x * f x) ≤ M * l2Norm μ f := by
  calc
    l2Norm μ (fun x => g x * f x) ≤ l2Norm μ (fun x => M * f x) := by
      apply l2Norm_mono (hf.const_smul M)
      filter_upwards [hbound] with x hx
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Real.norm_eq_abs, abs_of_nonneg hM]
      exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
    _ = M * l2Norm μ f := by rw [l2Norm_const_mul M hf, abs_of_nonneg hM]

lemma l2Norm_mono_measure {ν : Measure E} (hf : MemLp f 2 μ) (hν : ν ≤ μ) :
    l2Norm ν f ≤ l2Norm μ f :=
  ENNReal.toReal_mono hf.2.ne (eLpNorm_mono_measure f hν)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE L2Bounds

-- BEGIN COMPLETE MODULE CaccioppoliCore
section

open MeasureTheory Set

namespace HunterPDE.Regularity.Proof

theorem caccioppoli_core {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (f u η : EuclideanSpace ℝ (Fin n) → ℝ)
    (d : Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (U : H1Data Ω u) (V : H1Data Ω (fun x => η x ^ 2 * u x))
    (hsol : IsWeakSolution Ω a f u) (hf : MemLp f 2 (volume.restrict Ω))
    (hv : MemW0 1 2 Ω (fun x => η x ^ 2 * u x))
    (hV : ∀ j x, V.grad j x = η x ^ 2 * U.grad j x + 2 * η x * d j x * u x)
    (hηm : AEStronglyMeasurable η (volume.restrict Ω))
    (hdm : ∀ j, AEStronglyMeasurable (d j) (volume.restrict Ω))
    (ham : ∀ i j, AEStronglyMeasurable (a i j) (volume.restrict Ω))
    (M D θ : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) (hθ : 0 < θ)
    (hη : ∀ᵐ x ∂(volume.restrict Ω), |η x| ≤ 1)
    (ha : ∀ i j, ∀ᵐ x ∂(volume.restrict Ω), |a i j x| ≤ M)
    (hd : ∀ j, ∀ᵐ x ∂(volume.restrict Ω), |d j x| ≤ D)
    (hell : ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j) :
    gradientL2 (volume.restrict Ω) (fun i x => η x * U.grad i x) ≤
      (2 * (1 + 2 * (n : ℝ) ^ 2 * M * D) / θ + 1) *
        (l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u) := by
  let μ := volume.restrict Ω
  let g : Fin n → EuclideanSpace ℝ (Fin n) → ℝ := fun i x => η x * U.grad i x
  let X := gradientL2 μ g
  let F := l2Norm μ f
  let N := l2Norm μ u
  have hg (i : Fin n) : MemLp (g i) 2 μ :=
    memLp_mul_of_bound (U.grad_memLp i) hηm 1 zero_le_one hη
  have had (i j : Fin n) : ∀ᵐ x ∂μ, |a i j x * d j x| ≤ M * D := by
    filter_upwards [ha i j, hd j] with x hx hy
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hM
  have hcLp (i j : Fin n) : MemLp (fun x => a i j x * d j x * u x) 2 μ :=
    memLp_mul_of_bound U.self_memLp ((ham i j).mul (hdm j)) (M * D)
      (mul_nonneg hM hD) (had i j)
  have hm (i j : Fin n) : Integrable (fun x => a i j x * g i x * g j x) μ :=
    coefficient_product_integrable (hg i) (hg j) (ham i j) M (ha i j)
  have hc (i j : Fin n) : Integrable (fun x => g i x * (a i j x * d j x * u x)) μ :=
    (hg i).integrable_mul (hcLp i j)
  have hid := weak_solution_witness_identity hΩ hsol U V hv
  simp_rw [hV] at hid
  rw [cutoff_bilinear_identity a U.grad d η u hm hc] at hid
  have hell' : θ * X ^ 2 ≤ ∑ i, ∑ j, ∫ x, a i j x * g i x * g j x ∂μ := by
    rw [show X ^ 2 = ∑ i, l2Norm μ (g i) ^ 2 from gradientL2_sq μ g]
    apply elliptic_integral_bound a g hg θ hm
    filter_upwards [hell] with x hx
    exact hx (fun i => g i x)
  have hη2 : ∀ᵐ x ∂μ, |η x ^ 2| ≤ 1 := by
    filter_upwards [hη] with x hx
    rw [abs_pow]
    nlinarith [abs_nonneg (η x)]
  have hηuLp : MemLp (fun x => η x ^ 2 * u x) 2 μ :=
    memLp_mul_of_bound U.self_memLp (hηm.pow 2) 1 zero_le_one hη2
  have hr : (∫ x, f x * (η x ^ 2 * u x) ∂μ) ≤ F * N := by
    apply (le_abs_self _).trans
    apply (abs_integral_mul_le_l2 hf hηuLp).trans
    have hh := l2Norm_mul_le U.self_memLp 1 zero_le_one hη2
    simpa only [one_mul] using mul_le_mul_of_nonneg_left hh (l2Norm_nonneg μ f)
  have hb (i j : Fin n) : -(∫ x, g i x * (a i j x * d j x * u x) ∂μ) ≤
      X * (M * D * N) := by
    apply (neg_le_abs _).trans
    apply (abs_integral_mul_le_l2 (hg i) (hcLp i j)).trans
    exact mul_le_mul (l2Norm_le_gradientL2 μ g i)
      (l2Norm_mul_le U.self_memLp (M * D) (mul_nonneg hM hD) (had i j))
      (l2Norm_nonneg _ _) (gradientL2_nonneg μ g)
  have hsum : -(∑ i, ∑ j, ∫ x, g i x * (a i j x * d j x * u x) ∂μ) ≤
      (n : ℝ) ^ 2 * X * (M * D * N) := by
    have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb i j))
    simpa only [Finset.sum_neg_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, pow_two, mul_assoc] using hh
  have henergy : θ * X ^ 2 ≤ F * N + (2 * (n : ℝ) ^ 2 * M * D) * N * X := by
    change (∑ i, ∑ j, ∫ x, a i j x * g i x * g j x ∂μ) +
      2 * (∑ i, ∑ j, ∫ x, g i x * (a i j x * d j x * u x) ∂μ) = _ at hid
    nlinarith
  exact energy_bound_two_inputs hθ (by positivity) (gradientL2_nonneg μ g)
    (l2Norm_nonneg μ f) (l2Norm_nonneg μ u) henergy

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CaccioppoliCore

-- BEGIN COMPLETE MODULE TestDerivatives
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma test_partial {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Shared.IsTestFunction Ω φ) (i : Fin n) :
    Shared.IsTestFunction Ω (Shared.partialDeriv φ i) := by
  refine ⟨?_,hφ.2.1.fderiv_apply ℝ _,(tsupport_fderiv_apply_subset ℝ _).trans hφ.2.2⟩
  exact (hφ.1.fderiv_right (by simp)).clm_apply contDiff_const

lemma test_multi {φ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Shared.IsTestFunction Ω φ) (α : Fin n → ℕ) :
    Shared.IsTestFunction Ω (Shared.multiDeriv φ α) := by
  unfold Shared.multiDeriv
  induction Shared.multiIndexList α with
  | nil => exact hφ
  | cons i l ih => exact test_partial ih i

lemma test_mul {φ ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hφ : Shared.IsTestFunction Ω φ) (hψ : ContDiff ℝ ∞ ψ) :
    Shared.IsTestFunction Ω (fun x => φ x*ψ x) :=
  ⟨hφ.1.mul hψ,hφ.2.1.mul_right,(tsupport_mul_subset_left).trans hφ.2.2⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE TestDerivatives

-- BEGIN COMPLETE MODULE WeakLinear
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {α : Fin n → ℕ}

lemma weak_sub {f g u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Shared.HasWeakDeriv Ω α f u) (hg : Shared.HasWeakDeriv Ω α g v) :
    Shared.HasWeakDeriv Ω α (f-g) (u-v) := by
  refine ⟨hf.1.sub hg.1,hf.2.1.sub hg.2.1,?_⟩
  intro φ hφ
  have ht := test_multi hφ α
  simp only [Pi.sub_apply,sub_mul]
  rw [integral_sub (test_mul_integrable hf.2.1 hφ).integrableOn
      (test_mul_integrable hg.2.1 hφ).integrableOn,
    integral_sub (test_mul_integrable hf.1 ht).integrableOn
      (test_mul_integrable hg.1 ht).integrableOn,hf.2.2 φ hφ,hg.2.2 φ hφ]
  ring

lemma weak_const_mul {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Shared.HasWeakDeriv Ω α f g) (c : ℝ) :
    Shared.HasWeakDeriv Ω α (fun x => c*f x) (fun x => c*g x) := by
  refine ⟨hf.1.smul c,hf.2.1.smul c,?_⟩
  intro φ hφ
  simp only [mul_assoc]
  rw [integral_const_mul,integral_const_mul,hf.2.2 φ hφ]
  ring

lemma weak_restrict {Ω' : Set (EuclideanSpace ℝ (Fin n))} (hs : Ω'⊆Ω)
    {f g : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Shared.HasWeakDeriv Ω α f g) :
    Shared.HasWeakDeriv Ω' α f g := by
  refine ⟨hf.1.mono_set hs,hf.2.1.mono_set hs,?_⟩
  intro φ hφ
  have ht : Shared.IsTestFunction Ω φ := ⟨hφ.1,hφ.2.1,hφ.2.2.trans hs⟩
  have hh := hf.2.2 φ ht
  rw [test_integral_eq ht,test_integral_eq (test_multi ht α)] at hh
  rw [test_integral_eq hφ,test_integral_eq (test_multi hφ α)]
  exact hh

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakLinear

-- BEGIN COMPLETE MODULE WeakProduct
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma partial_mul {f g : EuclideanSpace ℝ (Fin n) → ℝ} (i : Fin n) (x : EuclideanSpace ℝ (Fin n))
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    Shared.partialDeriv (fun x => f x*g x) i x =
      Shared.partialDeriv f i x*g x+f x*Shared.partialDeriv g i x := by
  unfold Shared.partialDeriv
  change (fderiv ℝ (f*g) x) _ = _
  rw [fderiv_mul hf hg]
  simp only [add_apply,smul_apply,smul_eq_mul]
  ring

lemma weak_mul_smooth (hΩ : IsOpen Ω) {u g η : EuclideanSpace ℝ (Fin n) → ℝ} (i : Fin n)
    (hu : Shared.HasWeakDeriv Ω (Pi.single i 1) u g) (hη : ContDiff ℝ ∞ η) :
    Shared.HasWeakDeriv Ω (Pi.single i 1) (fun x => u x*η x)
      (fun x => g x*η x+u x*Shared.partialDeriv η i x) := by
  have hdη : ContDiff ℝ ∞ (Shared.partialDeriv η i) :=
    (hη.fderiv_right (by simp)).clm_apply contDiff_const
  have hU := hu.1.mul_continuousOn hη.continuous.continuousOn hΩ.isLocallyClosed
  have hG := hu.2.1.mul_continuousOn hη.continuous.continuousOn hΩ.isLocallyClosed
  have hE := hu.1.mul_continuousOn hdη.continuous.continuousOn hΩ.isLocallyClosed
  refine ⟨hU,hG.add hE,?_⟩
  intro φ hφ
  have hh := hu.2.2 (fun x => φ x*η x) (test_mul hφ hη)
  have hsum : (∑j : Fin n,(Pi.single i 1 : Fin n → ℕ) j)=1 := by simp
  simp only [multiDeriv_single,hsum,pow_one] at hh ⊢
  have hleft : (∫x in Ω,g x*(φ x*η x))=∫x in Ω,(g x*η x)*φ x := by
    apply integral_congr_ae; filter_upwards with x; ring
  have hright : (∫x in Ω,u x*Shared.partialDeriv (fun x => φ x*η x) i x)=
      (∫x in Ω,(u x*η x)*Shared.partialDeriv φ i x)+(∫x in Ω,(u x*Shared.partialDeriv η i x)*φ x) := by
    rw [← integral_add (test_mul_integrable hU (test_partial hφ i)).integrableOn
      (test_mul_integrable hE hφ).integrableOn]
    apply integral_congr_ae
    filter_upwards with x
    rw [partial_mul i x (hφ.1.differentiable (by simp) x) (hη.differentiable (by simp) x)]
    ring
  rw [hleft,hright] at hh
  simp only [add_mul]
  rw [integral_add (test_mul_integrable hG hφ).integrableOn (test_mul_integrable hE hφ).integrableOn]
  linarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakProduct

-- BEGIN COMPLETE MODULE WeakCutoffGlobal
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma weak_mul_test_global {u g η : EuclideanSpace ℝ (Fin n) → ℝ} (i : Fin n)
    (hu : Shared.HasWeakDeriv Ω (Pi.single i 1) u g) (hη : Shared.IsTestFunction Ω η) :
    Shared.HasWeakDeriv Set.univ (Pi.single i 1) (fun x => u x*η x)
      (fun x => g x*η x+u x*Shared.partialDeriv η i x) := by
  have hU := test_mul_integrable hu.1 hη
  have hG := test_mul_integrable hu.2.1 hη
  have hE := test_mul_integrable hu.1 (test_partial hη i)
  refine ⟨hU.locallyIntegrable.locallyIntegrableOn _,
    (hG.add hE).locallyIntegrable.locallyIntegrableOn _,?_⟩
  intro φ hφ
  have ht := test_mul hη hφ.1
  have hh := hu.2.2 (fun x => η x*φ x) ht
  rw [test_integral_eq ht,test_integral_eq (test_multi ht (Pi.single i 1))] at hh
  have hsum : (∑j : Fin n,(Pi.single i 1 : Fin n → ℕ) j)=1 := by simp
  simp only [multiDeriv_single,hsum,pow_one,Measure.restrict_univ] at hh ⊢
  have hleft : (∫x,g x*(η x*φ x))=∫x,(g x*η x)*φ x := by
    apply integral_congr_ae; filter_upwards with x; ring
  have hright : (∫x,u x*Shared.partialDeriv (fun x => η x*φ x) i x)=
      (∫x,(u x*η x)*Shared.partialDeriv φ i x)+(∫x,(u x*Shared.partialDeriv η i x)*φ x) := by
    rw [← integral_add
      (test_mul_integrable (hU.locallyIntegrable.locallyIntegrableOn univ) (test_partial hφ i))
      (test_mul_integrable (hE.locallyIntegrable.locallyIntegrableOn univ) hφ)]
    apply integral_congr_ae
    filter_upwards with x
    rw [partial_mul i x (hη.1.differentiable (by simp) x) (hφ.1.differentiable (by simp) x)]
    ring
  rw [hleft,hright] at hh
  simp only [add_mul]
  rw [integral_add
    (test_mul_integrable (hG.locallyIntegrable.locallyIntegrableOn univ) hφ)
    (test_mul_integrable (hE.locallyIntegrable.locallyIntegrableOn univ) hφ)]
  linarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakCutoffGlobal

-- BEGIN COMPLETE MODULE H1Cutoff
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma memLp_mul_test_global (hΩ : MeasurableSet Ω) {u η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemLp u 2 (volume.restrict Ω)) (hη : Shared.IsTestFunction Ω η) :
    MemLp (fun x => u x*η x) 2 volume := by
  have hi : MemLp (Ω.indicator u) 2 volume := (memLp_indicator_iff_restrict hΩ).mpr hu
  have hηLp : MemLp η ∞ volume := hη.1.continuous.memLp_top_of_hasCompactSupport hη.2.1 volume
  have hp : MemLp (fun x => Ω.indicator u x*η x) 2 volume := hηLp.mul' hi
  have he : (fun x => Ω.indicator u x*η x)=(fun x => u x*η x) := by
    funext x
    by_cases hx : x∈Ω
    · rw [indicator_of_mem hx]
    · have hz : η x=0 := by
        by_contra hh
        exact hx (hη.2.2 (subset_tsupport η hh))
      simp [hz]
  exact he ▸ hp

noncomputable def H1Data.cutoff {u η : EuclideanSpace ℝ (Fin n) → ℝ} (H : H1Data Ω u)
    (hΩ : IsOpen Ω) (hη : Shared.IsTestFunction Ω η) :
    H1Data univ (fun x => u x*η x) where
  grad i x := H.grad i x*η x+u x*Shared.partialDeriv η i x
  self_memLp := by simpa only [Measure.restrict_univ] using memLp_mul_test_global hΩ.measurableSet H.self_memLp hη
  weak i := weak_mul_test_global i (H.weak i) hη
  grad_memLp i := by
    rw [Measure.restrict_univ]
    convert!
      (memLp_mul_test_global hΩ.measurableSet (H.grad_memLp i) hη).add
      (memLp_mul_test_global hΩ.measurableSet H.self_memLp (test_partial hη i)) using 1

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H1Cutoff

-- BEGIN COMPLETE MODULE TranslateCalculus
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}

lemma partial_translate {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : Differentiable ℝ f)
    (z x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    Shared.partialDeriv (fun x => f (x+z)) i x = Shared.partialDeriv f i (x+z) := by
  unfold Shared.partialDeriv
  have hd := (hf (x+z)).hasFDerivAt.comp x ((hasFDerivAt_id x).add_const z)
  have he := congrArg (fun L => L (EuclideanSpace.single i (1:ℝ))) hd.fderiv
  simpa only [Function.comp_def,id_eq,ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using he

lemma test_translate {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Shared.IsTestFunction univ f) (z : EuclideanSpace ℝ (Fin n)) :
    Shared.IsTestFunction univ (fun x => f (x+z)) := by
  refine ⟨hf.1.comp (contDiff_id.add contDiff_const),?_,subset_univ _⟩
  exact hf.2.1.comp_homeomorph (Homeomorph.addRight z)

lemma integral_translate_pair (f g : EuclideanSpace ℝ (Fin n) → ℝ) (z : EuclideanSpace ℝ (Fin n)) :
    (∫x,f (x+z)*g x)=∫x,f x*g (x-z) := by
  rw [← integral_add_right_eq_self (fun x => f x*g (x-z)) z]
  simp only [add_sub_cancel_right]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE TranslateCalculus

-- BEGIN COMPLETE MODULE H1Translation
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}

lemma memLp_translate {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : MemLp u 2 volume) (z : EuclideanSpace ℝ (Fin n)) :
    MemLp (fun x => u (x+z)) 2 volume :=
  hu.comp_measurePreserving (measurePreserving_add_right volume z)

lemma weak_first_translate {u g : EuclideanSpace ℝ (Fin n) → ℝ} (i : Fin n)
    (hu : Shared.HasWeakDeriv univ (Pi.single i 1) u g)
    (huLp : MemLp u 2 volume) (hgLp : MemLp g 2 volume) (z : EuclideanSpace ℝ (Fin n)) :
    Shared.HasWeakDeriv univ (Pi.single i 1) (fun x => u (x+z)) (fun x => g (x+z)) := by
  refine ⟨(memLp_translate huLp z).locallyIntegrable (by norm_num) |>.locallyIntegrableOn _,
    (memLp_translate hgLp z).locallyIntegrable (by norm_num) |>.locallyIntegrableOn _,?_⟩
  intro φ hφ
  have ht := test_translate hφ (-z)
  have hh := hu.2.2 (fun x => φ (x+(-z))) ht
  have hsum : (∑j : Fin n,(Pi.single i 1 : Fin n → ℕ) j)=1 := by simp
  simp only [multiDeriv_single,hsum,pow_one,Measure.restrict_univ] at hh ⊢
  simp_rw [partial_translate (hφ.1.differentiable (by simp)) (-z) _ i] at hh
  rw [integral_translate_pair g φ z,integral_translate_pair u (Shared.partialDeriv φ i) z]
  simpa only [sub_eq_add_neg] using hh

noncomputable def H1Data.translate {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (H : H1Data univ u) (z : EuclideanSpace ℝ (Fin n)) : H1Data univ (fun x => u (x+z)) where
  grad i x := H.grad i (x+z)
  self_memLp := by
    simpa only [Measure.restrict_univ] using memLp_translate
      (by simpa only [Measure.restrict_univ] using H.self_memLp) z
  weak i := weak_first_translate i (H.weak i)
    (by simpa only [Measure.restrict_univ] using H.self_memLp)
    (by simpa only [Measure.restrict_univ] using H.grad_memLp i) z
  grad_memLp i := by
    simpa only [Measure.restrict_univ] using memLp_translate
      (by simpa only [Measure.restrict_univ] using H.grad_memLp i) z

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H1Translation

-- BEGIN COMPLETE MODULE H1Operations
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

noncomputable def H1Data.sub {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (H : H1Data Ω u) (J : H1Data Ω v) : H1Data Ω (u-v) where
  grad i := H.grad i-J.grad i
  self_memLp := H.self_memLp.sub J.self_memLp
  weak i := weak_sub (H.weak i) (J.weak i)
  grad_memLp i := (H.grad_memLp i).sub (J.grad_memLp i)

noncomputable def H1Data.const_mul {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (H : H1Data Ω u) (c : ℝ) : H1Data Ω (fun x => c*u x) where
  grad i x := c*H.grad i x
  self_memLp := H.self_memLp.const_mul c
  weak i := weak_const_mul (H.weak i) c
  grad_memLp i := (H.grad_memLp i).const_mul c

noncomputable def H1Data.restrict {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (H : H1Data Ω u) {Ω' : Set (EuclideanSpace ℝ (Fin n))} (hs : Ω'⊆Ω) : H1Data Ω' u where
  grad := H.grad
  self_memLp := H.self_memLp.mono_measure (Measure.restrict_mono hs le_rfl)
  weak i := weak_restrict hs (H.weak i)
  grad_memLp i := (H.grad_memLp i).mono_measure (Measure.restrict_mono hs le_rfl)

noncomputable def H1Data.quotient {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (H : H1Data univ u) (i : Fin n) (h : ℝ) : H1Data univ (diffQuot i h u) := by
  let J := ((H.translate (h • EuclideanSpace.single i 1)).sub H).const_mul h⁻¹
  convert! J using 1
  funext x
  simp only [diffQuot,Pi.sub_apply,div_eq_mul_inv,mul_comm]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H1Operations

-- BEGIN COMPLETE MODULE WeakCongruence
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))} {α : Fin n → ℕ}

lemma weak_congr {u v g h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Shared.HasWeakDeriv Ω α u g) (huv : u =ᵐ[volume.restrict Ω] v)
    (hgh : g =ᵐ[volume.restrict Ω] h) : Shared.HasWeakDeriv Ω α v h := by
  refine ⟨LocallyIntegrableOn.congr huv hu.1,LocallyIntegrableOn.congr hgh hu.2.1,?_⟩
  intro φ hφ
  calc
    _ = ∫x in Ω,g x*φ x := integral_congr_ae (hgh.mono (fun x hx => by simpa only using congrArg (fun t : ℝ => t * φ x) hx.symm))
    _ = _ := hu.2.2 φ hφ
    _ = _ := by
      congr 1
      exact integral_congr_ae (huv.mono (fun x hx => by simpa only using congrArg (fun t : ℝ => t * Shared.multiDeriv φ α x) hx))

lemma weak_zero (Ω : Set (EuclideanSpace ℝ (Fin n))) (α : Fin n → ℕ) :
    Shared.HasWeakDeriv Ω α 0 0 := by
  refine ⟨(locallyIntegrable_zero).locallyIntegrableOn _,(locallyIntegrable_zero).locallyIntegrableOn _,?_⟩
  intro φ _
  simp

lemma weak_vanish_outside_support {u g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : Shared.HasWeakDeriv univ α u g) :
    ∀ᵐ x ∂volume, x∉tsupport u → g x=0 := by
  have hr := weak_restrict (subset_univ (tsupport u)ᶜ) hu
  have he : u =ᵐ[volume.restrict (tsupport u)ᶜ] (0 : EuclideanSpace ℝ (Fin n) → ℝ) := by
    filter_upwards [ae_restrict_mem (isClosed_tsupport u).isOpen_compl.measurableSet] with x hx
    exact image_eq_zero_of_notMem_tsupport hx
  have hz := weakDeriv_unique (isClosed_tsupport u).isOpen_compl
    (weak_congr hr he Filter.EventuallyEq.rfl) (weak_zero (tsupport u)ᶜ α)
  change ∀ᵐ x ∂volume.restrict (tsupport u)ᶜ,g x=0 at hz
  rwa [ae_restrict_iff' (isClosed_tsupport u).isOpen_compl.measurableSet] at hz

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakCongruence

-- BEGIN COMPLETE MODULE SquaredCutoff
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def H1Data.squaredCutoff {u η : E → ℝ} (H : H1Data Ω u)
    (hΩ : IsOpen Ω) (hη : Shared.IsTestFunction Ω η) :
    H1Data univ (fun x => η x ^ 2 * u x) := by
  let η2 : E → ℝ := fun x => η x * η x
  have ht : Shared.IsTestFunction Ω η2 := test_mul hη hη.1
  let J := H.cutoff hΩ ht
  have hfun : (fun x => u x * η2 x) = (fun x => η x ^ 2 * u x) := by funext x; dsimp [η2]; ring
  have hgrad (i : Fin n) : J.grad i = (fun x => η x ^ 2 * H.grad i x +
      2 * η x * Shared.partialDeriv η i x * u x) := by
    funext x
    change H.grad i x * (η x * η x) + u x * Shared.partialDeriv η2 i x = _
    rw [partial_mul i x (hη.1.differentiable (by simp) x) (hη.1.differentiable (by simp) x)]
    ring
  refine ⟨(fun i x => η x ^ 2 * H.grad i x + 2 * η x * Shared.partialDeriv η i x * u x),
    hfun ▸ J.self_memLp, ?_, ?_⟩
  · intro i
    rw [← hfun, ← hgrad i]
    exact J.weak i
  · intro i
    rw [← hgrad i]
    exact J.grad_memLp i

lemma squaredCutoff_grad {u η : E → ℝ} (H : H1Data Ω u)
    (hΩ : IsOpen Ω) (hη : Shared.IsTestFunction Ω η) (i : Fin n) (x : E) :
    (H.squaredCutoff hΩ hη).grad i x = η x ^ 2 * H.grad i x +
      2 * η x * Shared.partialDeriv η i x * u x := rfl

lemma squaredCutoff_support {u η : E → ℝ} (hη : HasCompactSupport η) :
    HasCompactSupport (fun x => η x ^ 2 * u x) ∧
      tsupport (fun x => η x ^ 2 * u x) ⊆ tsupport η := by
  have hs : Function.support (fun x => η x ^ 2 * u x) ⊆ Function.support η := by
    intro x hx
    by_contra hh
    simp only [Function.mem_support, not_not] at hh
    simp [hh] at hx
  have ht : tsupport (fun x => η x ^ 2 * u x) ⊆ tsupport η := closure_mono hs
  exact ⟨hη.of_isClosed_subset (isClosed_tsupport _) ht, ht⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SquaredCutoff

-- BEGIN COMPLETE MODULE CompactGradient
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}

lemma compact_gradient (H : H1Data univ u) (hu : HasCompactSupport u) (i : Fin n) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ,
      Shared.HasWeakDeriv univ (Pi.single i 1) u g ∧
      MemLp g 2 volume ∧ HasCompactSupport g ∧ Integrable g volume ∧
      g =ᵐ[volume] H.grad i := by
  let K := tsupport u
  let g := K.indicator (H.grad i)
  have he : g =ᵐ[volume] H.grad i := by
    filter_upwards [weak_vanish_outside_support (H.weak i)] with x hx
    by_cases h : x∈K
    · simp [g,h]
    · simp [g,h,hx h]
  have hg : MemLp g 2 volume := by
    have hi := H.grad_memLp i
    rw [Measure.restrict_univ] at hi
    exact hi.ae_eq he.symm
  have hs : tsupport g ⊆ K := by
    apply closure_minimal Set.support_indicator_subset (isClosed_tsupport u)
  have hc : HasCompactSupport g := hu.of_isClosed_subset (isClosed_tsupport g) hs
  let : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hu.measure_lt_top.ne
  have hgi : IntegrableOn g K volume :=
    (hg.restrict K).integrable (by norm_num)
  have hglob : Integrable g volume :=
    (integrableOn_iff_integrable_of_support_subset ((subset_tsupport g).trans hs)).mp hgi
  refine ⟨g,weak_congr (H.weak i) Filter.EventuallyEq.rfl ?_,hg,hc,hglob,he⟩
  simpa using he.symm

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CompactGradient

-- BEGIN COMPLETE MODULE LpTranslation
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}

noncomputable def translationMap (z : EuclideanSpace ℝ (Fin n)) :
    C(EuclideanSpace ℝ (Fin n),EuclideanSpace ℝ (Fin n)) :=
  ⟨fun x => x+z,continuous_id.add continuous_const⟩

lemma translationMap_continuous : Continuous (translationMap (n := n)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) => z.2+z.1)
  fun_prop

noncomputable def lpTranslate (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (z : EuclideanSpace ℝ (Fin n)) : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  Lp.compMeasurePreserving (translationMap z) (measurePreserving_add_right volume z) f

lemma lpTranslate_continuous (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Continuous (lpTranslate f) := by
  exact continuous_const.compMeasurePreservingLp translationMap_continuous
    (fun z => measurePreserving_add_right volume z) (by norm_num)

lemma lpTranslate_zero (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    lpTranslate f 0=f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume (0 : EuclideanSpace ℝ (Fin n)))] with x hx
  simpa [lpTranslate,translationMap] using hx

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE LpTranslation

-- BEGIN COMPLETE MODULE LpMollifier
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}

noncomputable def lpSmooth (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n))) :=
  ∫z,ρ z • lpTranslate f (-z)

lemma lp_smooth_integrable (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    Integrable (fun z => ρ z • lpTranslate f (-z)) volume := by
  exact (hc.smul ((lpTranslate_continuous f).comp continuous_neg)).integrable_of_hasCompactSupport
    hs.smul_right

lemma lp_smooth_sub (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (hm : ∫z,ρ z=1)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    lpSmooth ρ f-f=∫z,ρ z • (lpTranslate f (-z)-f) := by
  have hf : Integrable (fun z => ρ z • f) volume :=
    (hc.integrable_of_hasCompactSupport hs).smul_const f
  simp_rw [smul_sub]
  rw [integral_sub (lp_smooth_integrable ρ hc hs f) hf,integral_smul_const,hm,one_smul]
  rfl

lemma lp_smooth_error (ρ : EuclideanSpace ℝ (Fin n) → ℝ) (hc : Continuous ρ)
    (hs : HasCompactSupport ρ) (hm : ∫z,ρ z=1) (hpos : ∀z,0≤ρ z)
    (f : Lp ℝ 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) (ε : ℝ)
    (he : ∀z∈Function.support ρ,‖lpTranslate f (-z)-f‖≤ε) :
    ‖lpSmooth ρ f-f‖≤ε := by
  rw [lp_smooth_sub ρ hc hs hm f]
  have hb : Integrable (fun z => ρ z*ε) volume :=
    (hc.integrable_of_hasCompactSupport hs).mul_const ε
  calc
    _ ≤ ∫z,ρ z*ε := norm_integral_le_of_norm_le hb (by
      filter_upwards with z
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (hpos z)]
      by_cases hz : ρ z=0
      · simp [hz]
      · exact mul_le_mul_of_nonneg_left (he z hz) (hpos z))
    _ = ε := by rw [integral_mul_const,hm,one_mul]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE LpMollifier

-- BEGIN COMPLETE MODULE SmallMollifier
section

open MeasureTheory Set Filter Metric
open scoped Topology ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma small_mollifier {J : Type*} [Fintype J]
    (f : J → Lp ℝ 2 (volume : Measure E)) (ε r : ℝ) (hε : 0<ε) (hr : 0<r) :
    ∃ρ : E → ℝ, Shared.IsTestFunction (ball 0 r) ρ ∧
      (∀z,0≤ρ z) ∧ (∫z,ρ z)=1 ∧ ∀j,‖lpSmooth ρ (f j)-f j‖<ε := by
  have he : ∀ᶠ z : E in 𝓝 0,∀j,‖lpTranslate (f j) (-z)-f j‖<ε/2 := by
    rw [eventually_all]
    intro j
    have hc : Continuous (fun z : E => ‖lpTranslate (f j) (-z)-f j‖) := (((lpTranslate_continuous (f j)).comp continuous_neg).sub continuous_const).norm
    have hh : ‖lpTranslate (f j) (-(0:E))-f j‖<ε/2 := by
      simp only [neg_zero,lpTranslate_zero,sub_self,norm_zero]
      positivity
    exact hc.continuousAt.eventually (gt_mem_nhds hh)
  obtain ⟨δ,hδ,heδ⟩ := Metric.eventually_nhds_iff.mp he
  let s := min δ r / 2
  have hs : 0<s := by dsimp [s]; positivity
  let b : ContDiffBump (0:E) := ⟨s/2,s,by positivity,by linarith⟩
  refine ⟨b.normed volume,⟨b.contDiff_normed,b.hasCompactSupport_normed,?_⟩,
    b.nonneg_normed,b.integral_normed,?_⟩
  · rw [b.tsupport_normed_eq]
    intro z hz
    have hsr : s<r := by dsimp [s]; have := min_le_right δ r; linarith
    exact (mem_closedBall.mp hz).trans_lt hsr
  · intro j
    apply lt_of_le_of_lt (lp_smooth_error _ b.continuous_normed b.hasCompactSupport_normed
      b.integral_normed b.nonneg_normed (f j) (ε/2) ?_) (by linarith)
    intro z hz
    rw [b.support_normed_eq] at hz
    have hsd : s<δ := by dsimp [s]; have := min_le_left δ r; linarith
    exact (heδ ((mem_ball.mp hz).trans hsd) j).le

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SmallMollifier

-- BEGIN COMPLETE MODULE ConvolutionPairing
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def smoothScalar (ρ u : E → ℝ) : E → ℝ :=
  convolution ρ u (ContinuousLinearMap.mul ℝ ℝ)

lemma smoothScalar_pair (ρ u φ : E → ℝ) (hρ : Integrable ρ volume)
    (hu : Integrable u volume) (hφ : Continuous φ) (hs : HasCompactSupport φ) :
    ∫x,φ x*smoothScalar ρ u x = ∫z,ρ z*(∫x,φ x*u (x-z)) := by
  obtain ⟨C,hC⟩ := hφ.bounded_above_of_compact_support hs
  have hi : Integrable (fun p : E×E => ρ p.2*u (p.1-p.2)*φ p.1) (volume.prod volume) :=
    (hρ.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hu).mul_bdd
      (hφ.comp continuous_fst).aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.1)
  calc
    _ = ∫x,∫z,ρ z*u (x-z)*φ x := by
      congr 1; ext x
      rw [smoothScalar,convolution,← integral_const_mul]
      congr 1; ext z; simp only [ContinuousLinearMap.mul_apply']; ring
    _ = ∫z,∫x,ρ z*u (x-z)*φ x := integral_integral_swap hi
    _ = _ := by
      congr 1; ext z
      rw [← integral_const_mul]
      congr 1; ext x; ring

lemma lpTranslate_pair (u φ : E → ℝ) (hu : MemLp u 2 volume)
    (hφ : MemLp φ 2 volume) (z : E) :
    inner ℝ (hφ.toLp φ) (lpTranslate (hu.toLp u) (-z)) = ∫x,φ x*u (x-z) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  have ht := Lp.coeFn_compMeasurePreserving (hu.toLp u)
    (measurePreserving_add_right volume (-z))
  have he := (measurePreserving_add_right volume (-z)).quasiMeasurePreserving.ae_eq_comp hu.coeFn_toLp
  filter_upwards [hφ.coeFn_toLp,ht,he] with x hx hy hz
  simp only [RCLike.inner_apply, conj_trivial]
  rw [mul_comm]
  rw [hx]
  change (lpTranslate (hu.toLp u) (-z) x) = (hu.toLp u) (x + -z) at hy
  change (hu.toLp u) (x + -z) = u (x + -z) at hz
  rw [hy,hz]
  rfl

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE ConvolutionPairing

-- BEGIN COMPLETE MODULE MollifierIdentification
section

open MeasureTheory Set
open scoped ENNReal ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma lp_pair (φ : E → ℝ) (hφ : MemLp φ 2 volume)
    (v : Lp ℝ 2 (volume : Measure E)) :
    inner ℝ (hφ.toLp φ) v = ∫x,φ x*v x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hφ.coeFn_toLp] with x hx
  simp only [RCLike.inner_apply,conj_trivial,hx]
  ring

lemma smoothScalar_ae_lpSmooth (ρ u : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : HasCompactSupport ρ) (hu : MemLp u 2 volume) (hiu : Integrable u volume) :
    smoothScalar ρ u =ᵐ[volume] lpSmooth ρ (hu.toLp u) := by
  have hc : ContDiff ℝ ∞ (smoothScalar ρ u) :=
    hsρ.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hρ hiu.locallyIntegrable
  apply ae_eq_of_integral_contDiff_smul_eq hc.continuous.locallyIntegrable
    ((Lp.memLp (lpSmooth ρ (hu.toLp u))).locallyIntegrable (by norm_num))
  intro φ hφ hsφ
  have hφp : MemLp φ 2 volume := hφ.continuous.memLp_of_hasCompactSupport hsφ
  simp only [smul_eq_mul]
  rw [smoothScalar_pair ρ u φ (hρ.continuous.integrable_of_hasCompactSupport hsρ)
    hiu hφ.continuous hsφ,← lp_pair φ hφp]
  change _ = inner ℝ (hφp.toLp φ) (∫z,ρ z • lpTranslate (hu.toLp u) (-z))
  rw [← integral_inner (lp_smooth_integrable ρ hρ.continuous hsρ (hu.toLp u))]
  congr 1; ext z
  rw [real_inner_smul_right,lpTranslate_pair u φ hu hφp z]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE MollifierIdentification

-- BEGIN COMPLETE MODULE ScalarMollifierError
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma smoothScalar_memLp (ρ u : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : HasCompactSupport ρ) (hu : MemLp u 2 volume) (hiu : Integrable u volume) :
    MemLp (smoothScalar ρ u) 2 volume :=
  (Lp.memLp _).ae_eq (smoothScalar_ae_lpSmooth ρ u hρ hsρ hu hiu).symm

lemma smoothScalar_error (ρ u : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : HasCompactSupport ρ) (hu : MemLp u 2 volume) (hiu : Integrable u volume) :
    l2Norm volume (u-smoothScalar ρ u) = ‖lpSmooth ρ (hu.toLp u)-hu.toLp u‖ := by
  have hv := smoothScalar_memLp ρ u hρ hsρ hu hiu
  have he : hv.toLp (smoothScalar ρ u) = lpSmooth ρ (hu.toLp u) := by
    apply Lp.ext
    exact hv.coeFn_toLp.trans (smoothScalar_ae_lpSmooth ρ u hρ hsρ hu hiu)
  rw [l2Norm,← Lp.norm_toLp _ (hu.sub hv),MemLp.toLp_sub hu hv,he,norm_sub_rev]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE ScalarMollifierError

-- BEGIN COMPLETE MODULE ReflectedTest
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma test_reflect (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hsρ : HasCompactSupport ρ)
    (x : E) : Shared.IsTestFunction univ (fun y => ρ (x-y)) := by
  refine ⟨hρ.comp (contDiff_const.sub contDiff_id),?_,subset_univ _⟩
  exact hsρ.comp_homeomorph (Homeomorph.subLeft x)

lemma partial_reflect (ρ : E → ℝ) (hρ : Differentiable ℝ ρ) (x y : E) (i : Fin n) :
    Shared.partialDeriv (fun y => ρ (x-y)) i y = -Shared.partialDeriv ρ i (x-y) := by
  unfold Shared.partialDeriv
  have hd := (hρ (x-y)).hasFDerivAt.comp y ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  have he := congrArg (fun L => L (EuclideanSpace.single i (1:ℝ))) hd.fderiv
  simpa only [Function.comp_def,ContinuousLinearMap.comp_apply,sub_apply,
    zero_apply,neg_apply,ContinuousLinearMap.id_apply,zero_sub,map_neg] using he

lemma weak_reflected_integral (ρ u g : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : HasCompactSupport ρ) (i : Fin n)
    (hu : Shared.HasWeakDeriv univ (Pi.single i 1) u g) (x : E) :
    (∫y,g y*ρ (x-y)) = ∫y,u y*Shared.partialDeriv ρ i (x-y) := by
  have hh := hu.2.2 _ (test_reflect ρ hρ hsρ x)
  have hsum : (∑j : Fin n,(Pi.single i 1 : Fin n → ℕ) j)=1 := by simp
  simp only [Measure.restrict_univ,multiDeriv_single,hsum,pow_one] at hh
  simp_rw [partial_reflect ρ (hρ.differentiable (by simp)),mul_neg,integral_neg] at hh
  simpa using hh

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE ReflectedTest

-- BEGIN COMPLETE MODULE MollifierDerivative
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma smoothScalar_comm (ρ u : E → ℝ) :
    smoothScalar ρ u = convolution u ρ (ContinuousLinearMap.mul ℝ ℝ) := by
  unfold smoothScalar
  have he : (ContinuousLinearMap.mul ℝ ℝ).flip = ContinuousLinearMap.mul ℝ ℝ := by
    ext; rfl
  simpa only [he] using (convolution_flip (L := ContinuousLinearMap.mul ℝ ℝ) (f := u) (g := ρ) (μ := volume))

lemma smoothScalar_partial (ρ u g : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hsρ : HasCompactSupport ρ) (i : Fin n)
    (hu : Shared.HasWeakDeriv univ (Pi.single i 1) u g) :
    Shared.partialDeriv (smoothScalar ρ u) i = smoothScalar ρ g := by
  have hul : LocallyIntegrable u volume := by simpa only [locallyIntegrableOn_univ] using hu.1
  have hρ1 : ContDiff ℝ 1 ρ := hρ.of_le (by simp)
  funext x
  rw [smoothScalar_comm,Shared.partialDeriv,
    (hsρ.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ) hul hρ1 x).fderiv]
  rw [convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ) hul
    (hsρ.fderiv ℝ) (hρ1.continuous_fderiv one_ne_zero)]
  rw [smoothScalar_comm]
  change (∫y,u y*Shared.partialDeriv ρ i (x-y)) = ∫y,g y*ρ (x-y)
  exact (weak_reflected_integral ρ u g hρ hsρ i hu x).symm

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE MollifierDerivative

-- BEGIN COMPLETE MODULE MollifierSupport
section

open MeasureTheory Set Metric
open scoped Pointwise
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma smoothScalar_support (ρ u : E → ℝ) (r : ℝ)
    (hρ : tsupport ρ ⊆ ball 0 r) :
    tsupport (smoothScalar ρ u) ⊆ cthickening r (tsupport u) := by
  apply closure_minimal _ isClosed_cthickening
  intro x hx
  have hm := support_convolution_subset (ContinuousLinearMap.mul ℝ ℝ) hx
  obtain ⟨z,hz,y,hy,rfl⟩ := hm
  apply mem_cthickening_of_dist_le (z+y) y r (tsupport u) (subset_tsupport u hy)
  have hz' := hρ (subset_tsupport ρ hz)
  simpa only [dist_eq_norm,add_sub_cancel_right,sub_zero] using (mem_ball.mp hz').le

lemma smoothScalar_test {Ω : Set E} {r : ℝ} (ρ u : E → ℝ)
    (hρ : Shared.IsTestFunction (ball 0 r) ρ) (hu : HasCompactSupport u)
    (hlu : LocallyIntegrable u volume) (hs : tsupport (smoothScalar ρ u) ⊆ Ω) :
    Shared.IsTestFunction Ω (smoothScalar ρ u) := by
  refine ⟨hρ.2.1.contDiff_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hρ.1 hlu,
    hρ.2.1.convolution (ContinuousLinearMap.mul ℝ ℝ) hu,hs⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE MollifierSupport

-- BEGIN COMPLETE MODULE CompactH1Approximation
section

open MeasureTheory Set Metric
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma integrable_of_memLp_compact {u : E → ℝ} (hu : MemLp u 2 volume)
    (hs : HasCompactSupport u) : Integrable u volume := by
  let : IsFiniteMeasure (volume.restrict (tsupport u)) := isFiniteMeasure_restrict.mpr hs.measure_lt_top.ne
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport u)).mp
    ((hu.restrict (tsupport u)).integrable (by norm_num))

lemma compact_h1_approximation {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (H : H1Data univ u) (hs : HasCompactSupport u) (hsub : tsupport u ⊆ Ω)
    (ε : ℝ) (hε : 0<ε) :
    ∃φ : E → ℝ,Shared.IsTestFunction Ω φ ∧
      l2Norm volume (u-φ)<ε ∧
      ∀i,l2Norm volume (H.grad i-Shared.partialDeriv φ i)<ε := by
  classical
  have hup : MemLp u 2 volume := by simpa using H.self_memLp
  have hui := integrable_of_memLp_compact hup hs
  choose g hgw hgp hgs hgi hge using compact_gradient H hs
  let F : Option (Fin n) → E → ℝ := fun j => match j with
    | none => u
    | some i => g i
  have hFp : ∀j,MemLp (F j) 2 volume := by intro j; cases j with
    | none => exact hup
    | some i => exact hgp i
  have hFi : ∀j,Integrable (F j) volume := by intro j; cases j with
    | none => exact hui
    | some i => exact hgi i
  obtain ⟨r,hr,hrΩ⟩ := hs.exists_cthickening_subset_open hΩ hsub
  obtain ⟨ρ,hρ,hρpos,hρmass,hρerr⟩ :=
    small_mollifier (fun j => (hFp j).toLp (F j)) ε r hε hr
  let φ := smoothScalar ρ u
  have hφ : Shared.IsTestFunction Ω φ := smoothScalar_test ρ u hρ hs hui.locallyIntegrable
    ((smoothScalar_support ρ u r hρ.2.2).trans hrΩ)
  refine ⟨φ,hφ,?_,?_⟩
  · rw [show φ=smoothScalar ρ u from rfl,smoothScalar_error ρ u hρ.1 hρ.2.1 hup hui]
    exact hρerr none
  · intro i
    have hp : Shared.partialDeriv φ i=smoothScalar ρ (g i) :=
      smoothScalar_partial ρ u (g i) hρ.1 hρ.2.1 i (hgw i)
    rw [hp]
    have he : (H.grad i-smoothScalar ρ (g i)) =ᵐ[volume] (g i-smoothScalar ρ (g i)) :=
      (hge i).symm.sub Filter.EventuallyEq.rfl
    rw [l2Norm,eLpNorm_congr_ae he]
    change l2Norm volume (g i-smoothScalar ρ (g i))<ε
    rw [smoothScalar_error ρ (g i) hρ.1 hρ.2.1 (hgp i) (hgi i)]
    exact hρerr (some i)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CompactH1Approximation

-- BEGIN COMPLETE MODULE H1NormBound
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

lemma sobolev_two_le_sum (k : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) :
    sobolevNorm k 2 Ω u ≤ ∑α∈multiIndicesLe n k,
      eLpNorm (Shared.weakDeriv Ω α u) 2 (volume.restrict Ω) := by
  unfold sobolevNorm
  simp only [ENNReal.ofNat_ne_top,if_false,ENNReal.toReal_ofNat]
  simp only [ENNReal.rpow_two]
  have hh := Finset.sum_sq_le_sq_sum_of_nonneg
    (s := multiIndicesLe n k) (f := fun α => eLpNorm (Shared.weakDeriv Ω α u) 2 (volume.restrict Ω))
    (fun _ _ => zero_le)
  apply (ENNReal.rpow_le_rpow hh (by positivity : (0:ℝ)≤1/2)).trans_eq
  rw [← ENNReal.rpow_natCast,← ENNReal.rpow_mul]
  norm_num

lemma H1Data.sobolev_le_card {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (H : H1Data Ω u) (hΩ : IsOpen Ω) (δ : ℝ≥0∞)
    (h0 : eLpNorm u 2 (volume.restrict Ω)≤δ)
    (hg : ∀i,eLpNorm (H.grad i) 2 (volume.restrict Ω)≤δ) :
    sobolevNorm 1 2 Ω u ≤ (multiIndicesLe n 1).card*δ := by
  apply (sobolev_two_le_sum 1 u).trans
  calc
    _ ≤ ∑_α∈multiIndicesLe n 1,δ := by
      apply Finset.sum_le_sum
      intro α hα
      rcases order_one_cases ((multi_mem_iff 1 α).mp hα) with rfl | ⟨i,rfl⟩
      · rw [eLpNorm_congr_ae (chosen_weakDeriv_ae hΩ (weak_zero_self (memLp_locally H.self_memLp)))]
        exact h0
      · rw [eLpNorm_congr_ae (chosen_weakDeriv_ae hΩ (H.weak i))]
        exact hg i
    _ = _ := by simp

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H1NormBound

-- BEGIN COMPLETE MODULE SmoothWeak
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}

lemma smooth_weak_first {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : Fin n) :
    Shared.HasWeakDeriv univ (Pi.single i 1) f (Shared.partialDeriv f i) := by
  have hd : ContDiff ℝ ∞ (Shared.partialDeriv f i) :=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  have hfl : LocallyIntegrableOn f univ volume := hf.continuous.locallyIntegrable.locallyIntegrableOn univ
  have hdl : LocallyIntegrableOn (Shared.partialDeriv f i) univ volume := hd.continuous.locallyIntegrable.locallyIntegrableOn univ
  refine ⟨hfl,hdl,?_⟩
  intro φ hφ
  have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (test_mul_integrable hdl hφ)
    (test_mul_integrable hfl (test_partial hφ i))
    (test_mul_integrable hfl hφ)
    (fun x _ => hf.differentiable (by simp) x)
    (fun x _ => hφ.1.differentiable (by simp) x)
  have hsum : (∑j : Fin n,(Pi.single i 1 : Fin n → ℕ) j)=1 := by simp
  simp only [Measure.restrict_univ,multiDeriv_single,hsum,pow_one]
  change (∫x,Shared.partialDeriv f i x*φ x)=(-1)*(∫x,f x*Shared.partialDeriv φ i x)
  change (∫x,f x*Shared.partialDeriv φ i x)=-(∫x,Shared.partialDeriv f i x*φ x) at hh
  linarith

lemma test_h1Data {Ω : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : Shared.IsTestFunction Ω f) : Nonempty (H1Data Ω f) := by
  refine ⟨⟨Shared.partialDeriv f,?_,?_,?_⟩⟩
  · exact (hf.1.continuous.memLp_of_hasCompactSupport hf.2.1 (p := 2)).restrict Ω
  · intro i
    exact weak_restrict (subset_univ Ω) (smooth_weak_first hf.1 i)
  · intro i
    exact ((test_partial hf i).1.continuous.memLp_of_hasCompactSupport
      (test_partial hf i).2.1 (p := 2)).restrict Ω

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SmoothWeak

-- BEGIN COMPLETE MODULE CompactH1Zero
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma eLpNorm_le_of_l2_lt {u : E → ℝ} (hu : MemLp u 2 volume) {δ : ℝ}
    (h : l2Norm volume u<δ) : eLpNorm u 2 volume≤ENNReal.ofReal δ := by
  rw [← ENNReal.ofReal_toReal hu.2.ne]
  exact ENNReal.ofReal_le_ofReal h.le

lemma compact_h1_memW0 {Ω : Set E} (hΩ : IsOpen Ω) {u : E → ℝ}
    (H : H1Data univ u) (hs : HasCompactSupport u) (hsub : tsupport u ⊆ Ω) :
    MemW0 1 2 Ω u := by
  refine ⟨(H.restrict (subset_univ Ω)).memW,?_⟩
  intro ε hε
  obtain ⟨δ,hδ,hδε⟩ := ENNReal.exists_nnreal_pos_mul_lt
    (a := ((multiIndicesLe n 1).card : ℝ≥0∞)) (by simp) (ne_of_gt hε)
  obtain ⟨φ,hφ,h0,hg⟩ := compact_h1_approximation hΩ H hs hsub (δ:ℝ) hδ
  let Hφ : H1Data univ φ :=
    ⟨Shared.partialDeriv φ,by simpa using hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1 (p := 2),
      fun i => smooth_weak_first hφ.1 i,fun i => by
        simpa using (test_partial hφ i).1.continuous.memLp_of_hasCompactSupport
          (test_partial hφ i).2.1 (p := 2)⟩
  let D := (H.sub Hφ).restrict (subset_univ Ω)
  have hp0 : MemLp (u-φ) 2 volume := by simpa using (H.sub Hφ).self_memLp
  have hpg (i : Fin n) : MemLp (H.grad i-Shared.partialDeriv φ i) 2 volume := by
    simpa [Hφ,H1Data.sub] using (H.sub Hφ).grad_memLp i
  refine ⟨φ,hφ,(D.sobolev_le_card hΩ (δ:ℝ≥0∞) ?_ ?_).trans_lt ?_⟩
  · exact (eLpNorm_restrict_le _ _ _ _).trans (by simpa using eLpNorm_le_of_l2_lt hp0 h0)
  · intro i
    exact (eLpNorm_restrict_le _ _ _ _).trans (by
      simpa [D,H1Data.restrict,H1Data.sub,Hφ] using eLpNorm_le_of_l2_lt (hpg i) (hg i))
  · simpa only [mul_comm] using hδε

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CompactH1Zero

-- BEGIN COMPLETE MODULE UniformEssentialBounds
section

open MeasureTheory
open scoped ENNReal
namespace HunterPDE.Regularity.Proof

theorem finite_essential_bound {E ι : Type*} [MeasurableSpace E] [Fintype ι]
    {μ : Measure E} (a : ι → E → ℝ) (ha : ∀ i, MemLp (a i) ∞ μ) :
    ∃ M : ℝ, 0 < M ∧ ∀ i, ∀ᵐ x ∂μ, |a i x| ≤ M := by
  classical
  let M : ℝ := 1 + ∑ i, |lpNorm (a i) ∞ μ|
  refine ⟨M, by dsimp [M]; positivity, ?_⟩
  intro i
  filter_upwards [ae_le_lpNorm_exponent_top (ha i)] with x hx
  have hi : |lpNorm (a i) ∞ μ| ≤ ∑ j, |lpNorm (a j) ∞ μ| :=
    Finset.single_le_sum (fun j _ => abs_nonneg (lpNorm (a j) ∞ μ)) (Finset.mem_univ i)
  have hb := le_abs_self (lpNorm (a i) ∞ μ)
  dsimp [M]
  rw [Real.norm_eq_abs] at hx
  linarith

theorem test_derivative_essential_bound {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} {η : EuclideanSpace ℝ (Fin n) → ℝ}
    (hη : Shared.IsTestFunction Ω η) :
    ∃ D : ℝ, 0 < D ∧ ∀ i, ∀ᵐ x ∂volume, |Shared.partialDeriv η i x| ≤ D := by
  apply finite_essential_bound
  intro i
  exact (test_partial hη i).1.continuous.memLp_top_of_hasCompactSupport
    (test_partial hη i).2.1 volume

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE UniformEssentialBounds

-- BEGIN COMPLETE MODULE InteriorCutoff
section

open Set Metric
open scoped ContDiff Manifold

namespace HunterPDE.Regularity.Proof

/-- A smooth cutoff around a compact subset, with its closed support still inside the
original open set. No regularity of either boundary is required. -/
theorem interior_cutoff {n : ℕ} {K Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hKΩ : K ⊆ Ω) :
    ∃ η : EuclideanSpace ℝ (Fin n) → ℝ,
      Shared.IsTestFunction Ω η ∧ (∀ x, 0 ≤ η x ∧ η x ≤ 1) ∧
      (∀ x ∈ K, η x = 1) := by
  obtain ⟨V, hV, hKV, hVΩ, hVc⟩ := exists_open_between_and_isCompact_closure hK hΩ hKΩ
  obtain ⟨η, hη, hrange, hsupp, hone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞))
      𝓘(ℝ, EuclideanSpace ℝ (Fin n)) hV hK.isClosed hKV
  have hts : tsupport η = closure V := by rw [tsupport, hsupp]
  refine ⟨η, ⟨hη.contDiff, ?_, ?_⟩, ?_, ?_⟩
  · simpa only [HasCompactSupport, hts] using hVc
  · rw [hts]
    exact hVΩ
  · intro x
    exact hrange (mem_range_self x)
  · intro x hx
    exact (hone x).mp hx

theorem compactly_contained_intermediate {n : ℕ}
    {Ω' Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (h : CompactlyContained Ω' Ω) :
    ∃ U, CompactlyContained Ω' U ∧ CompactlyContained U Ω := by
  obtain ⟨U, hU, hsub, hcl, hcomp⟩ :=
    exists_open_between_and_isCompact_closure h.2.2.1 hΩ h.2.2.2
  refine ⟨U, ⟨h.1, h.2.1, h.2.2.1, hsub⟩, ?_⟩
  exact ⟨h.1.mono (subset_closure.trans hsub), hU, hcomp, hcl⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE InteriorCutoff

-- BEGIN COMPLETE MODULE LocalL2Bounds
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

lemma l2Norm_congr {f g : E → ℝ} (h : f =ᵐ[μ] g) : l2Norm μ f = l2Norm μ g := by
  unfold l2Norm
  rw [eLpNorm_congr_ae h]

lemma l2Norm_restrict_eqOn {s : Set E} (hs : MeasurableSet s) {f g : E → ℝ}
    (h : EqOn f g s) : l2Norm (μ.restrict s) f = l2Norm (μ.restrict s) g := by
  apply l2Norm_congr
  filter_upwards [ae_restrict_mem hs] with x hx
  exact h hx

lemma local_gradient_le_cutoff {n : ℕ} {Ω Ω' : Set E} (hs : Ω' ⊆ Ω)
    (hm : MeasurableSet Ω') (g : Fin n → E → ℝ) (η : E → ℝ)
    (hη : ∀ x ∈ Ω', η x = 1)
    (hg : ∀ i, MemLp (fun x => η x * g i x) 2 (μ.restrict Ω)) (i : Fin n) :
    l2Norm (μ.restrict Ω') (g i) ≤ gradientL2 (μ.restrict Ω) (fun j x => η x * g j x) := by
  calc
    _ = l2Norm (μ.restrict Ω') (fun x => η x * g i x) := by
      apply l2Norm_restrict_eqOn hm
      intro x hx
      simp [hη x hx]
    _ ≤ l2Norm (μ.restrict Ω) (fun x => η x * g i x) :=
      l2Norm_mono_measure (hg i) (Measure.restrict_mono hs le_rfl)
    _ ≤ _ := l2Norm_le_gradientL2 (μ.restrict Ω) (fun j x => η x * g j x) i

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE LocalL2Bounds

-- BEGIN COMPLETE MODULE CaccioppoliLocal
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof

 theorem interior_gradient_bound {n : ℕ}
    {Ω Ω' : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hΩ' : MeasurableSet Ω') (hK : IsCompact (closure Ω')) (hKΩ : closure Ω' ⊆ Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (θ : ℝ) (hθ : 0 < θ)
    (hell : ∀ᵐ x ∂(volume.restrict Ω), ∀ ξ : Fin n → ℝ,
      θ * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, a i j x * ξ i * ξ j) :
    ∃ C : ℝ, 0 < C ∧ ∀ f u (U : H1Data Ω u),
      IsWeakSolution Ω a f u → MemLp f 2 (volume.restrict Ω) →
      ∀ i, l2Norm (volume.restrict Ω') (U.grad i) ≤
        C * (l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u) := by
  obtain ⟨η,hη,hηbound,hηone⟩ := interior_cutoff hK hΩ hKΩ
  obtain ⟨M,hM,hMb⟩ := finite_essential_bound (fun ij : Fin n × Fin n => a ij.1 ij.2)
    (fun ij => ha ij.1 ij.2)
  obtain ⟨D,hD,hDb⟩ := test_derivative_essential_bound hη
  let C : ℝ := 2 * (1 + 2 * (n : ℝ) ^ 2 * M * D) / θ + 1
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro f u U hsol hf i
  let W := U.squaredCutoff hΩ hη
  let V := W.restrict (subset_univ Ω)
  have hs := squaredCutoff_support (u := u) hη.2.1
  have hv := compact_h1_memW0 hΩ W hs.1 (hs.2.trans hη.2.2)
  have hb : ∀ᵐ x ∂volume.restrict Ω, |η x| ≤ 1 :=
    Filter.Eventually.of_forall (fun x => by rw [abs_of_nonneg (hηbound x).1]; exact (hηbound x).2)
  have hd (j : Fin n) : ∀ᵐ x ∂volume.restrict Ω, |Shared.partialDeriv η j x| ≤ D :=
    ae_restrict_of_ae (hDb j)
  have hg (j : Fin n) : MemLp (fun x => η x * U.grad j x) 2 (volume.restrict Ω) :=
    memLp_mul_of_bound (U.grad_memLp j) hη.1.continuous.aestronglyMeasurable 1 zero_le_one hb
  have he := caccioppoli_core hΩ a f u η (Shared.partialDeriv η) U V hsol hf hv
    (fun j x => squaredCutoff_grad U hΩ hη j x)
    hη.1.continuous.aestronglyMeasurable
    (fun j => (test_partial hη j).1.continuous.aestronglyMeasurable)
    (fun j k => (ha j k).1) M D θ hM.le hD.le hθ hb
    (fun j k => hMb (j,k)) hd hell
  exact (local_gradient_le_cutoff (subset_closure.trans hKΩ) hΩ' U.grad η
    (fun x hx => hηone x (subset_closure hx)) hg i).trans he

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CaccioppoliLocal

-- BEGIN COMPLETE MODULE GlobalCutoffNorm
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma l2Norm_indicator {Ω : Set E} (hΩ : MeasurableSet Ω) (u : E → ℝ) :
    l2Norm volume (Ω.indicator u) = l2Norm (volume.restrict Ω) u := by
  unfold l2Norm
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hΩ]

lemma global_product_cutoff_bound {Ω : Set E} (hΩ : MeasurableSet Ω)
    {u η : E → ℝ} (hu : MemLp u 2 (volume.restrict Ω))
    (hs : Function.support η ⊆ Ω) {D : ℝ} (hD : 0 ≤ D)
    (hb : ∀ᵐ x ∂volume, |η x| ≤ D) :
    l2Norm volume (fun x => u x * η x) ≤ D * l2Norm (volume.restrict Ω) u := by
  have he : (fun x => u x * η x) = (fun x => η x * Ω.indicator u x) := by
    funext x
    by_cases hx : x ∈ Ω
    · simp [hx,mul_comm]
    · have hz : η x = 0 := by by_contra hh; exact hx (hs hh)
      simp [hz,hx]
  rw [he]
  have hp := (memLp_indicator_iff_restrict hΩ).mpr hu
  exact (l2Norm_mul_le hp D hD hb).trans_eq (by rw [l2Norm_indicator hΩ])

lemma cutoff_gradient_norm_bound {Ω U : Set E} (hΩ : IsOpen Ω) (hU : MeasurableSet U)
    {u χ : E → ℝ} (H : H1Data Ω u) (hχ : Shared.IsTestFunction Ω χ)
    (hUΩ : U ⊆ Ω) (hs : tsupport χ ⊆ U)
    (hχB : ∀ x, |χ x| ≤ 1) {D Y : ℝ} (hD : 0 ≤ D)
    (hd : ∀ i, ∀ᵐ x ∂volume, |Shared.partialDeriv χ i x| ≤ D)
    (hg : ∀ i, l2Norm (volume.restrict U) (H.grad i) ≤ Y) :
    ∀ i, l2Norm volume ((H.cutoff hΩ hχ).grad i) ≤
      Y + D * l2Norm (volume.restrict Ω) u := by
  intro i
  have h1 := memLp_mul_test_global hΩ.measurableSet (H.grad_memLp i) hχ
  have h2 := memLp_mul_test_global hΩ.measurableSet H.self_memLp (test_partial hχ i)
  have hu := (H.grad_memLp i).mono_measure (Measure.restrict_mono hUΩ le_rfl)
  have hb1 := global_product_cutoff_bound hU hu ((subset_tsupport χ).trans hs)
    zero_le_one (Filter.Eventually.of_forall hχB)
  have hb2 := global_product_cutoff_bound hΩ.measurableSet H.self_memLp
    ((subset_tsupport _).trans (test_partial hχ i).2.2) hD (hd i)
  have ha := l2Norm_add_le h1 h2
  change l2Norm volume (fun x => H.grad i x * χ x + u x * Shared.partialDeriv χ i x) ≤ _
  change l2Norm volume (fun x => H.grad i x * χ x + u x * Shared.partialDeriv χ i x) ≤ _ at ha
  simpa only [one_mul] using ha.trans (add_le_add (hb1.trans (by simpa using hg i)) hb2)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE GlobalCutoffNorm

-- BEGIN COMPLETE MODULE CompactCoefficientBounds
section

open Set Metric

namespace HunterPDE.Regularity.Proof

/-- Local C¹ coefficients have uniform value and derivative bounds on a fixed compact
collar; the bounds depend on the coefficients and the sets, not on a solution. -/
theorem compact_coefficient_bounds {n : ℕ}
    {Ω K : Set (EuclideanSpace ℝ (Fin n))} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω) :
    ∃ M : ℝ, 0 < M ∧ ∀ i j x, x ∈ K →
      |a i j x| ≤ M ∧ ‖fderiv ℝ (a i j) x‖ ≤ M := by
  classical
  have hb : ∀ i j, ∃ B : ℝ, ∀ x ∈ K,
      |a i j x| ≤ B ∧ ‖fderiv ℝ (a i j) x‖ ≤ B := by
    intro i j
    obtain ⟨B, hB⟩ := (hK.image_of_continuousOn ((ha i j).continuousOn.norm.mono hKΩ)).bddAbove
    obtain ⟨D, hD⟩ := (hK.image_of_continuousOn
      (((ha i j).continuousOn_fderiv_of_isOpen hΩ le_rfl).norm.mono hKΩ)).bddAbove
    refine ⟨max B D, fun x hx => ⟨?_, ?_⟩⟩
    · have hb : |a i j x| ≤ B := by simpa only [Real.norm_eq_abs] using hB ⟨x, hx, rfl⟩
      exact hb.trans (le_max_left _ _)
    · exact (hD ⟨x, hx, rfl⟩).trans (le_max_right _ _)
  choose B hB using hb
  refine ⟨1 + ∑ i, ∑ j, |B i j|, by positivity, ?_⟩
  intro i j x hx
  have hi : |B i j| ≤ ∑ i, ∑ j, |B i j| := by
    exact (Finset.single_le_sum (fun k _ => abs_nonneg (B i k)) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (fun k _ => Finset.sum_nonneg (fun l _ => abs_nonneg (B k l)))
        (Finset.mem_univ i))
  have hm : B i j ≤ 1 + ∑ i, ∑ j, |B i j| := by linarith [le_abs_self (B i j)]
  exact ⟨(hB i j x hx).1.trans hm, (hB i j x hx).2.trans hm⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CompactCoefficientBounds

-- BEGIN COMPLETE MODULE CoefficientQuotient
section

open Set Metric
namespace HunterPDE.Regularity.Proof

lemma coefficient_difference_bound {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) (a : EuclideanSpace ℝ (Fin n) → ℝ)
    (ha : ContDiffOn ℝ 1 a Ω) {M h : ℝ} (hh : h ≠ 0)
    (x : EuclideanSpace ℝ (Fin n)) (i : Fin n)
    (hseg : segment ℝ x (x + h • EuclideanSpace.single i 1) ⊆ Ω)
    (hbound : ∀ y ∈ segment ℝ x (x + h • EuclideanSpace.single i 1),
      ‖fderiv ℝ a y‖ ≤ M) : |diffQuot i h a x| ≤ M := by
  have hdiff : ∀ y ∈ segment ℝ x (x + h • EuclideanSpace.single i 1),
      DifferentiableAt ℝ a y := by
    intro y hy
    exact ((ha.differentiableOn (by norm_num)) y (hseg hy)).differentiableAt (hΩ.mem_nhds (hseg hy))
  have hb := (convex_segment x (x + h • EuclideanSpace.single i (1:ℝ))).norm_image_sub_le_of_norm_fderiv_le
    hdiff hbound (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)
  have he : ‖x + h • EuclideanSpace.single i (1:ℝ) - x‖ = |h| := by
    rw [add_sub_cancel_left, norm_smul]
    simp
  rw [he, Real.norm_eq_abs] at hb
  unfold diffQuot
  rw [abs_div]
  exact (div_le_iff₀ (abs_pos.mpr hh)).mpr hb

lemma compact_shift_collar {n : ℕ} {K Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hK : IsCompact K) (hΩ : IsOpen Ω) (hsub : K ⊆ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ∀ i : Fin n, ∀ t : ℝ, |t| ≤ ε →
      x + t • EuclideanSpace.single i 1 ∈ Ω := by
  obtain ⟨ε,hε,hεΩ⟩ := hK.exists_cthickening_subset_open hΩ hsub
  refine ⟨ε,hε,?_⟩
  intro x hx i t ht
  apply hεΩ
  apply mem_cthickening_of_dist_le (x + t • EuclideanSpace.single i 1) x ε K hx
  simpa [dist_eq_norm, norm_smul] using ht

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CoefficientQuotient

-- BEGIN COMPLETE MODULE CoefficientCollar
section

open Set Metric
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma coordinate_segment_in_collar {K : Set E} {ε h : ℝ} (hε : 0 ≤ ε)
    {x : E} (hx : x ∈ K) (i : Fin n) (hh : |h| ≤ ε) :
    segment ℝ x (x + h • EuclideanSpace.single i 1) ⊆ cthickening ε K := by
  have hright : x + h • EuclideanSpace.single i (1:ℝ) ∈ closedBall x ε := by
    simpa [mem_closedBall,dist_eq_norm,norm_smul] using hh
  have hseg := (convex_closedBall x ε).segment_subset (mem_closedBall_self hε) hright
  intro y hy
  exact mem_cthickening_of_dist_le y x ε K hx (hseg hy)

lemma coefficient_collar_bounds {Ω K : Set E} (hΩ : IsOpen Ω)
    (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (a : Fin n → Fin n → E → ℝ) (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω) :
    ∃ ε M : ℝ, 0 < ε ∧ 0 < M ∧
      ∀ (k i j : Fin n) (h : ℝ), h ≠ 0 → |h| ≤ ε → ∀ x ∈ K,
        x + h • EuclideanSpace.single k 1 ∈ Ω ∧
        |a i j (x + h • EuclideanSpace.single k 1)| ≤ M ∧
        |diffQuot k h (a i j) x| ≤ M := by
  obtain ⟨ε,hε,hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  obtain ⟨M,hM,hb⟩ := compact_coefficient_bounds hΩ (hK.cthickening (r := ε)) hsub a ha
  refine ⟨ε,M,hε,hM,?_⟩
  intro k i j h hh hsmall x hx
  have hs := coordinate_segment_in_collar hε.le hx k hsmall
  have hright := hs (right_mem_segment ℝ x (x + h • EuclideanSpace.single k 1))
  refine ⟨hsub hright,(hb i j _ hright).1,?_⟩
  exact coefficient_difference_bound hΩ (a i j) (ha i j) hh x k (hs.trans hsub)
    (fun y hy => (hb i j y (hs hy)).2)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CoefficientCollar

-- BEGIN COMPLETE MODULE InteriorH2Setup
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

structure InteriorSetup (Ω Ω' : Set E) (a : Fin n → Fin n → E → ℝ) where
  inner : Set E
  inner_open : IsOpen inner
  inner_subset : inner ⊆ Ω
  target_subset : Ω' ⊆ inner
  η : E → ℝ
  χ : E → ℝ
  η_test : Shared.IsTestFunction inner η
  η_bound : ∀ x, |η x| ≤ 1
  η_one : ∀ x ∈ Ω', η x = 1
  χ_test : Shared.IsTestFunction Ω χ
  χ_one : ∀ x ∈ inner, χ x = 1
  ε : ℝ
  M : ℝ
  D : ℝ
  C : ℝ
  ε_pos : 0 < ε
  M_pos : 0 < M
  D_pos : 0 < D
  C_pos : 0 < C
  shift_inner : ∀ (k : Fin n) (h : ℝ), |h| ≤ ε → ∀ x ∈ tsupport η,
    x + h • EuclideanSpace.single k 1 ∈ inner
  coefficient_bounds : ∀ (k i j : Fin n) (h : ℝ), h ≠ 0 → |h| ≤ ε → ∀ x ∈ tsupport η,
    |a i j (x + h • EuclideanSpace.single k 1)| ≤ M ∧ |diffQuot k h (a i j) x| ≤ M
  derivative_bound : ∀ i, ∀ᵐ x ∂volume, |Shared.partialDeriv η i x| ≤ D
  gradient_bound : ∀ f u (U : H1Data Ω u) (hΩ : IsOpen Ω),
    IsWeakSolution Ω a f u → MemLp f 2 (volume.restrict Ω) →
    ∀ i, l2Norm volume ((U.cutoff hΩ χ_test).grad i) ≤
      C * (l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u)

 theorem interior_setup_exists {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (hsub : CompactlyContained Ω' Ω) (a : Fin n → Fin n → E → ℝ)
    (ha : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (haL : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (θ : ℝ) (hell : UniformlyElliptic Ω a θ) : Nonempty (InteriorSetup Ω Ω' a) := by
  obtain ⟨V,hV0,hVΩ⟩ := compactly_contained_intermediate hΩ hsub
  obtain ⟨η,hη,hηB,hηone⟩ := interior_cutoff hV0.2.2.1 hVΩ.2.1 hV0.2.2.2
  obtain ⟨χ,hχ,hχB,hχone⟩ := interior_cutoff hVΩ.2.2.1 hΩ hVΩ.2.2.2
  obtain ⟨O,hO,hχO,hOΩ,hOc⟩ := exists_open_between_and_isCompact_closure hχ.2.1 hΩ hχ.2.2
  obtain ⟨Cg,hCg,hgrad⟩ := interior_gradient_bound hΩ hO.measurableSet hOc hOΩ a haL θ hell.1 hell.2
  obtain ⟨Dχ,hDχ,hDχB⟩ := test_derivative_essential_bound hχ
  obtain ⟨D,hD,hDB⟩ := test_derivative_essential_bound hη
  obtain ⟨ε1,hε1,hε1s⟩ := compact_shift_collar hη.2.1 hVΩ.2.1 hη.2.2
  obtain ⟨ε2,M,hε2,hM,hcoef⟩ := coefficient_collar_bounds hΩ hη.2.1
    (hη.2.2.trans (subset_closure.trans hVΩ.2.2.2)) a ha
  refine ⟨{
    inner := V, inner_open := hVΩ.2.1,
    inner_subset := subset_closure.trans hVΩ.2.2.2,
    target_subset := subset_closure.trans hV0.2.2.2,
    η := η, χ := χ, η_test := hη,
    η_bound := fun x => by rw [abs_of_nonneg (hηB x).1]; exact (hηB x).2,
    η_one := fun x hx => hηone x (subset_closure hx), χ_test := hχ,
    χ_one := fun x hx => hχone x (subset_closure hx),
    ε := min ε1 ε2, M := M, D := D, C := Cg+Dχ+1,
    ε_pos := lt_min hε1 hε2, M_pos := hM, D_pos := hD, C_pos := by positivity,
    shift_inner := ?_, coefficient_bounds := ?_, derivative_bound := hDB,
    gradient_bound := ?_ }⟩
  · intro k h hh x hx
    exact hε1s x hx k h (hh.trans (min_le_left _ _))
  · intro k i j h hh hsmall x hx
    exact (hcoef k i j h hh (hsmall.trans (min_le_right _ _)) x hx).2
  · intro f u U hΩu hsol hf i
    have hb := cutoff_gradient_norm_bound hΩu hO.measurableSet U hχ
      (subset_closure.trans hOΩ) hχO
      (fun x => by rw [abs_of_nonneg (hχB x).1]; exact (hχB x).2)
      hDχ.le hDχB (hgrad f u U hsol hf) i
    have hF := l2Norm_nonneg (volume.restrict Ω) f
    have hU := l2Norm_nonneg (volume.restrict Ω) u
    nlinarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE InteriorH2Setup

-- BEGIN COMPLETE MODULE L2DifferenceAdjoint
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem l2_difference_adjoint {n : ℕ}
    {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) (i : Fin n) (t : ℝ) :
    (∫ x, diffQuot i t f x * g x) = -(∫ x, f x * diffQuot i (-t) g x) := by
  let e := t • EuclideanSpace.single i (1 : ℝ)
  have hp : MemLp (fun x => f (x + e)) 2 volume :=
    hf.comp_measurePreserving (measurePreserving_add_right volume e)
  have hm : MemLp (fun x => g (x - e)) 2 volume :=
    hg.comp_measurePreserving (measurePreserving_sub_right volume e)
  have h0 : Integrable (fun x => f x * g x) volume := hf.integrable_mul hg
  have hplus : Integrable (fun x => f (x + e) * g x) volume := hp.integrable_mul hg
  have hminus : Integrable (fun x => f x * g (x - e)) volume := hf.integrable_mul hm
  have he : (∫ x, f (x + e) * g x) = ∫ x, f x * g (x - e) := by
    have h := integral_add_right_eq_self (μ := volume) (fun x => f x * g (x - e)) e
    simpa only [add_sub_cancel_right] using h
  calc
    (∫ x, diffQuot i t f x * g x) =
        ((∫ x, f (x + e) * g x) - ∫ x, f x * g x) / t := by
      rw [← integral_sub hplus h0, ← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [diffQuot, e]
      ring
    _ = ((∫ x, f x * g (x - e)) - ∫ x, f x * g x) / t := by rw [he]
    _ = -(∫ x, f x * diffQuot i (-t) g x) := by
      rw [← integral_sub hminus h0, ← integral_div, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [diffQuot, e]
      simp only [neg_smul, sub_eq_add_neg, div_neg]
      ring

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE L2DifferenceAdjoint

-- BEGIN COMPLETE MODULE DiscreteWeakIdentity
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma indicator_pair_integral {Ω : Set E} (hΩ : MeasurableSet Ω) (f g : E → ℝ) :
    (∫ x, Ω.indicator f x * g x) = ∫ x in Ω, f x * g x := by
  rw [← integral_indicator hΩ]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : x ∈ Ω <;> simp [hx]

 theorem discrete_weak_identity {Ω : Set E} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → E → ℝ) (f u w v : E → ℝ)
    (U : H1Data Ω u) (W : H1Data univ w) (V : H1Data Ω v)
    (hsol : IsWeakSolution Ω a f u) (hv : MemW0 1 2 Ω v)
    (hflux : ∀ i j, MemLp (fun x => a i j x * U.grad i x) 2 (volume.restrict Ω))
    (k : Fin n) (h : ℝ) (hval : ∀ x, v x = -diffQuot k (-h) w x)
    (hgrad : ∀ j x, V.grad j x = -diffQuot k (-h) (W.grad j) x) :
    (∑ i, ∑ j, ∫ x, diffQuot k h (Ω.indicator (fun y => a i j y * U.grad i y)) x *
      W.grad j x) = -(∫ x in Ω, f x * diffQuot k (-h) w x) := by
  have he := weak_solution_witness_identity hΩ hsol U V hv
  have hp (i j : Fin n) : MemLp (Ω.indicator (fun y => a i j y * U.grad i y)) 2 volume :=
    (memLp_indicator_iff_restrict hΩ.measurableSet).mpr (hflux i j)
  have hterm (i j : Fin n) :
      (∫ x, diffQuot k h (Ω.indicator (fun y => a i j y * U.grad i y)) x * W.grad j x) =
      ∫ x in Ω, a i j x * U.grad i x * V.grad j x := by
    rw [l2_difference_adjoint (hp i j) (by simpa using W.grad_memLp j),
      indicator_pair_integral hΩ.measurableSet]
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards with x
    rw [hgrad]
    ring
  simp_rw [hterm]
  rw [he, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  rw [hval]
  ring

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE DiscreteWeakIdentity

-- BEGIN COMPLETE MODULE QuotientH1Data
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ}

noncomputable def H1Data.quotientExplicit (H : H1Data univ u) (i : Fin n) (h : ℝ) :
    H1Data univ (diffQuot i h u) where
  grad j := diffQuot i h (H.grad j)
  self_memLp := (H.quotient i h).self_memLp
  grad_memLp j := by
    have hgp : MemLp (H.grad j) 2 volume := by simpa using H.grad_memLp j
    have hp := ((memLp_translate hgp (h•EuclideanSpace.single i 1)).sub hgp).const_mul h⁻¹
    simp only [Measure.restrict_univ]
    convert! hp using 1
    ext x; simp [diffQuot,div_eq_mul_inv,mul_comm]
  weak j := by
    have hup : MemLp u 2 volume := by simpa using H.self_memLp
    have hgp : MemLp (H.grad j) 2 volume := by simpa using H.grad_memLp j
    have hw := weak_const_mul (weak_sub
      (weak_first_translate j (H.weak j) hup hgp (h•EuclideanSpace.single i 1)) (H.weak j)) h⁻¹
    convert! hw using 1 <;> (ext x; simp [diffQuot,div_eq_mul_inv,mul_comm])

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE QuotientH1Data

-- BEGIN COMPLETE MODULE QuotientSupport
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma quotient_support (u : E → ℝ) (i : Fin n) (h : ℝ) :
    tsupport (diffQuot i h u) ⊆
      (fun x => x+h•EuclideanSpace.single i 1) ⁻¹' tsupport u ∪ tsupport u := by
  apply closure_minimal _
    (((isClosed_tsupport u).preimage (continuous_id.add continuous_const)).union (isClosed_tsupport u))
  intro x hx
  by_contra hn
  have hh : x+h•EuclideanSpace.single i 1∉tsupport u ∧ x∉tsupport u := by simpa using hn
  have ha := image_eq_zero_of_notMem_tsupport hh.1
  have hb := image_eq_zero_of_notMem_tsupport hh.2
  exact hx (by simp [diffQuot,ha,hb])

lemma quotient_compact {u : E → ℝ} (hu : HasCompactSupport u) (i : Fin n) (h : ℝ) :
    HasCompactSupport (diffQuot i h u) := by
  have ht : HasCompactSupport (fun x => u (x+h•EuclideanSpace.single i 1)) :=
    hu.comp_homeomorph (Homeomorph.addRight _)
  have he : diffQuot i h u = fun x => (u (x+h•EuclideanSpace.single i 1)-u x)*h⁻¹ := by
    ext x; simp only [diffQuot,div_eq_mul_inv]
  rw [he]
  exact (ht.sub hu).mul_right

lemma backward_quotient_support {Ω : Set E} {u : E → ℝ} {K : Set E}
    (hs : tsupport u ⊆ K) (i : Fin n) (h : ℝ)
    (hK : K⊆Ω) (hshift : ∀x∈K,x+h•EuclideanSpace.single i 1∈Ω) :
    tsupport (diffQuot i (-h) u) ⊆ Ω := by
  intro x hx
  rcases quotient_support u i (-h) hx with hx | hx
  · have hz := hshift (x+(-h)•EuclideanSpace.single i 1) (hs hx)
    simpa only [neg_smul,add_assoc,neg_add_cancel,add_zero] using hz
  · exact hK (hs hx)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE QuotientSupport

-- BEGIN COMPLETE MODULE DifferenceTestData
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def H1Data.differenceCutoff {u η : E → ℝ} (H : H1Data univ u)
    (hη : Shared.IsTestFunction Ω η) (i : Fin n) (h : ℝ) :
    H1Data univ (fun x => η x^2*diffQuot i h u x) :=
  (H.quotientExplicit i h).squaredCutoff isOpen_univ ⟨hη.1,hη.2.1,subset_univ _⟩

lemma differenceCutoff_grad {u η : E → ℝ} (H : H1Data univ u)
    (hη : Shared.IsTestFunction Ω η) (i j : Fin n) (h : ℝ) (x : E) :
    (H.differenceCutoff hη i h).grad j x =
      η x^2*diffQuot i h (H.grad j) x+2*η x*Shared.partialDeriv η j x*diffQuot i h u x := rfl

noncomputable def H1Data.backwardTest {w : E → ℝ} (W : H1Data univ w)
    (i : Fin n) (h : ℝ) : H1Data univ (fun x => -diffQuot i (-h) w x) := by
  let V := (W.quotientExplicit i (-h)).const_mul (-1)
  convert! V using 1
  ext x; simp

lemma backward_test_memW0 {w : E → ℝ} (W : H1Data univ w) (hΩ : IsOpen Ω)
    (hw : HasCompactSupport w) {K : Set E} (hK : tsupport w⊆K)
    (i : Fin n) (h : ℝ) (hsub : K⊆Ω)
    (hshift : ∀x∈K,x+h•EuclideanSpace.single i 1∈Ω) :
    MemW0 1 2 Ω (fun x => -diffQuot i (-h) w x) := by
  apply compact_h1_memW0 hΩ (W.backwardTest i h) (quotient_compact hw i (-h)).neg
  change tsupport (-diffQuot i (-h) w) ⊆ Ω
  rw [tsupport_neg]
  exact backward_quotient_support hK i h hsub hshift

lemma difference_test_memW0 {u η : E → ℝ} (H : H1Data univ u) (hΩ : IsOpen Ω)
    (hη : Shared.IsTestFunction Ω η) (i : Fin n) (h : ℝ)
    (hshift : ∀x∈tsupport η,x+h•EuclideanSpace.single i 1∈Ω) :
    MemW0 1 2 Ω (fun x => -diffQuot i (-h) (fun y => η y^2*diffQuot i h u y) x) := by
  exact backward_test_memW0 (H.differenceCutoff hη i h) hΩ
    (squaredCutoff_support hη.2.1).1 (squaredCutoff_support hη.2.1).2 i h hη.2.2 hshift

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE DifferenceTestData

-- BEGIN COMPLETE MODULE BackwardTestGradient
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def H1Data.backwardTestExplicit {w : E → ℝ} (W : H1Data univ w)
    (i : Fin n) (h : ℝ) : H1Data univ (fun x => -diffQuot i (-h) w x) where
  grad j x := -diffQuot i (-h) (W.grad j) x
  self_memLp := (W.backwardTest i h).self_memLp
  grad_memLp j := by
    have hp := ((W.quotientExplicit i (-h)).grad_memLp j).neg
    exact hp
  weak j := by
    have hw := weak_const_mul ((W.quotientExplicit i (-h)).weak j) (-1)
    convert! hw using 1 <;> (ext x; simp only [neg_one_mul] <;> rfl)

lemma backwardTestExplicit_grad {w : E → ℝ} (W : H1Data univ w)
    (i j : Fin n) (h : ℝ) (x : E) :
    (W.backwardTestExplicit i h).grad j x = -diffQuot i (-h) (W.grad j) x := rfl

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE BackwardTestGradient

-- BEGIN COMPLETE MODULE UnitIntervalSquare
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof

lemma unit_interval_square (g : ℝ → ℝ) (hg : ContinuousOn g (Icc 0 1)) :
    (∫t in Icc (0:ℝ) 1,g t)^2 ≤ ∫t in Icc (0:ℝ) 1,(g t)^2 := by
  have hi := hg.integrableOn_Icc (μ := volume)
  have hi2 : IntegrableOn (fun t => (g t)^2) (Icc (0:ℝ) 1) volume := (hg.pow 2).integrableOn_Icc
  let c := ∫t in Icc (0:ℝ) 1,g t
  have h : 0 ≤ ∫t in Icc (0:ℝ) 1,(g t-c)^2 := integral_nonneg (fun t => sq_nonneg (g t-c))
  have he : (fun t => (g t-c)^2) = fun t => (g t)^2-(2*c)*g t+c^2 := by funext t; ring
  rw [he] at h
  change 0 ≤ ∫t in Icc (0:ℝ) 1,((fun t => (g t)^2-(2*c)*g t) t + (fun _ : ℝ => c^2) t) at h
  have hadd := integral_add (μ := volume.restrict (Icc (0:ℝ) 1)) (f := fun t : ℝ => (g t)^2-(2*c)*g t)
    (g := fun _ : ℝ => c^2) (Integrable.sub hi2 (hi.const_mul (2*c))) (integrable_const (c^2))
  have hsub := integral_sub (μ := volume.restrict (Icc (0:ℝ) 1)) (f := fun t : ℝ => (g t)^2)
    (g := fun t => (2*c)*g t) hi2 (hi.const_mul (2*c))
  rw [hadd,hsub,integral_const_mul] at h
  norm_num [Real.volume_Icc] at h
  dsimp [c] at h
  nlinarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE UnitIntervalSquare

-- BEGIN COMPLETE MODULE SmoothQuotientFormula
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma smooth_quotient_formula (u : E → ℝ) (hu : ContDiff ℝ ∞ u)
    (i : Fin n) (h : ℝ) (hh : h≠0) (x : E) :
    diffQuot i h u x = ∫t in Icc (0:ℝ) 1,Shared.partialDeriv u i (x+(t*h)•EuclideanSpace.single i 1) := by
  let e : E := EuclideanSpace.single i 1
  have hd (t : ℝ) : HasDerivAt (fun t => u (x+(t*h)•e))
      (h*Shared.partialDeriv u i (x+(t*h)•e)) t := by
    have ht : HasDerivAt (fun t : ℝ => x+(t*h)•e) (h•e) t := by
      simpa only [id_eq,one_mul] using (((hasDerivAt_id t).mul_const h).smul_const e).const_add x
    convert! (hu.differentiable (by simp) (x+(t*h)•e)).hasFDerivAt.comp_hasDerivAt t ht using 1
    simp [Shared.partialDeriv,e,map_smul]
  have hc : Continuous (fun t : ℝ => h*Shared.partialDeriv u i (x+(t*h)•e)) := by
    have hpd : ContDiff ℝ ∞ (Shared.partialDeriv u i) :=
      (hu.fderiv_right (by simp)).clm_apply contDiff_const
    have hp := hpd.continuous
    exact continuous_const.mul (hp.comp (continuous_const.add ((continuous_id.mul continuous_const).smul continuous_const)))
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (_ : t∈uIcc (0:ℝ) 1) => hd t) (hc.intervalIntegrable 0 1)
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ)≤1),integral_const_mul] at hi
  rw [← integral_Icc_eq_integral_Ioc] at hi
  simp only [one_mul,zero_mul,zero_smul,add_zero] at hi
  unfold diffQuot
  apply (div_eq_iff hh).mpr
  simpa only [mul_comm] using hi.symm

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SmoothQuotientFormula

-- BEGIN COMPLETE MODULE TranslatedSquareIntegral
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma translated_square_integrable (g : E → ℝ) (hg : Continuous g)
    (hi : Integrable (fun x => (g x)^2) volume) (v : E) :
    Integrable (fun p : ℝ×E => (g (p.2+p.1•v))^2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod volume) := by
  have hm : AEStronglyMeasurable (fun p : ℝ×E => (g (p.2+p.1•v))^2)
      ((volume.restrict (Icc (0:ℝ) 1)).prod volume) := by
    apply Continuous.aestronglyMeasurable
    exact (hg.comp (continuous_snd.add (continuous_fst.smul continuous_const))).pow 2
  rw [integrable_prod_iff hm]
  refine ⟨Filter.Eventually.of_forall (fun t => hi.comp_add_right (t•v)),?_⟩
  have he : (fun t : ℝ => ∫x,‖(g (x+t•v))^2‖) = fun _ => ∫x,(g x)^2 := by
    funext t
    simp only [Real.norm_eq_abs,abs_sq]
    exact integral_add_right_eq_self (fun x => (g x)^2) (t•v)
  rw [he]
  exact integrable_const _

lemma translated_square_integral (g : E → ℝ) (hg : Continuous g)
    (hi : Integrable (fun x => (g x)^2) volume) (v : E) :
    (∫x,∫t in Icc (0:ℝ) 1,(g (x+t•v))^2) = ∫x,(g x)^2 := by
  rw [← integral_integral_swap (translated_square_integrable g hg hi v)]
  simp_rw [integral_add_right_eq_self (fun x => (g x)^2)]
  norm_num [Real.volume_Icc]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE TranslatedSquareIntegral

-- BEGIN COMPLETE MODULE QuotientL2Algebra
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma l2Norm_sub_le {u v : E → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    l2Norm volume (u-v)≤l2Norm volume u+l2Norm volume v := by
  rw [l2Norm,← Lp.norm_toLp _ (hu.sub hv),MemLp.toLp_sub hu hv]
  simpa only [Lp.norm_toLp,l2Norm] using norm_sub_le (hu.toLp u) (hv.toLp v)

lemma l2Norm_translate {u : E → ℝ} (hu : MemLp u 2 volume) (z : E) :
    l2Norm volume (fun x => u (x+z))=l2Norm volume u := by
  unfold l2Norm
  exact congrArg ENNReal.toReal (eLpNorm_comp_measurePreserving (p := 2) hu.aestronglyMeasurable (measurePreserving_add_right volume z))

lemma l2Norm_const_mul_global {u : E → ℝ} (hu : MemLp u 2 volume) (c : ℝ) :
    l2Norm volume (fun x => c*u x)=|c| *l2Norm volume u := by
  have he : (fun x => c*u x)=c•u := rfl
  rw [he,l2Norm,← Lp.norm_toLp _ (hu.const_smul c),MemLp.toLp_const_smul c hu,norm_smul,Lp.norm_toLp]
  rfl

lemma quotient_memLp {u : E → ℝ} (hu : MemLp u 2 volume) (i : Fin n) (h : ℝ) :
    MemLp (diffQuot i h u) 2 volume := by
  convert ((memLp_translate hu (h•EuclideanSpace.single i 1)).sub hu).const_mul h⁻¹ using 1
  ext x; simp [diffQuot,div_eq_mul_inv,mul_comm]

lemma quotient_l2_coarse {u : E → ℝ} (hu : MemLp u 2 volume) (i : Fin n) (h : ℝ) :
    l2Norm volume (diffQuot i h u)≤(2/|h|)*l2Norm volume u := by
  have he : diffQuot i h u = fun x => h⁻¹*((fun x : E => u (x+h•EuclideanSpace.single i 1))-u) x := by
    ext x; simp [diffQuot,div_eq_mul_inv,mul_comm]
  rw [he,l2Norm_const_mul_global ((memLp_translate hu _).sub hu)]
  have hb := l2Norm_sub_le (memLp_translate hu (h•EuclideanSpace.single i 1)) hu
  rw [l2Norm_translate hu] at hb
  calc
    _ ≤ |h⁻¹| *(l2Norm volume u+l2Norm volume u) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = _ := by rw [abs_inv]; ring

lemma quotient_sub (u v : E → ℝ) (i : Fin n) (h : ℝ) :
    diffQuot i h (u-v)=diffQuot i h u-diffQuot i h v := by
  ext x; simp only [diffQuot,Pi.sub_apply]; ring

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE QuotientL2Algebra

-- BEGIN COMPLETE MODULE SmoothQuotientBound
section

open MeasureTheory Set
open scoped ContDiff
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma smooth_quotient_l2_bound {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (hs : HasCompactSupport u) (i : Fin n) (h : ℝ) :
    l2Norm volume (diffQuot i h u)≤l2Norm volume (Shared.partialDeriv u i) := by
  by_cases hh : h=0
  · subst h
    have he : diffQuot i 0 u=0 := by ext x; simp [diffQuot]
    rw [he]
    simpa only [l2Norm,eLpNorm_zero,ENNReal.toReal_zero] using l2Norm_nonneg volume (Shared.partialDeriv u i)
  let g := Shared.partialDeriv u i
  have hgd : ContDiff ℝ ∞ g := (hu.fderiv_right (by simp)).clm_apply contDiff_const
  have hg : Continuous g := hgd.continuous
  have hgs : HasCompactSupport g := hs.fderiv_apply ℝ (EuclideanSpace.single i 1)
  have hgp : MemLp g 2 volume := hg.memLp_of_hasCompactSupport hgs
  have hup : MemLp u 2 volume := hu.continuous.memLp_of_hasCompactSupport hs
  have hqp := quotient_memLp hup i h
  have hp (x : E) : (diffQuot i h u x)^2≤∫t in Icc (0:ℝ) 1,(g (x+t•(h•EuclideanSpace.single i 1)))^2 := by
    rw [smooth_quotient_formula u hu i h hh x]
    have hcont : Continuous (fun t : ℝ => g (x+t•(h•EuclideanSpace.single i 1))) := by
      fun_prop
    simpa only [g,smul_smul] using unit_interval_square
      (fun t : ℝ => g (x+t•(h•EuclideanSpace.single i 1)))
      hcont.continuousOn
  have hj := translated_square_integrable g hg hgp.integrable_sq (h•EuclideanSpace.single i 1)
  have hb := integral_mono hqp.integrable_sq hj.integral_prod_right hp
  rw [translated_square_integral g hg hgp.integrable_sq,
    integral_sq_eq_l2_sq hqp,integral_sq_eq_l2_sq hgp] at hb
  nlinarith [l2Norm_nonneg volume (diffQuot i h u),l2Norm_nonneg volume g]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SmoothQuotientBound

-- BEGIN COMPLETE MODULE CompactQuotientBound
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma l2Norm_le_sub_add {u v : E → ℝ} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    l2Norm volume u≤l2Norm volume (u-v)+l2Norm volume v := by
  have he : u=(u-v)+v := by ext x; simp
  calc
    _ = l2Norm volume ((u-v)+v) := congrArg (l2Norm volume) he
    _ ≤ _ := l2Norm_add_le (hu.sub hv) hv

lemma compact_quotient_l2_bound {u : E → ℝ} (H : H1Data univ u)
    (hs : HasCompactSupport u) (i : Fin n) (h : ℝ) :
    l2Norm volume (diffQuot i h u)≤l2Norm volume (H.grad i) := by
  have hup : MemLp u 2 volume := by simpa using H.self_memLp
  have hgp : MemLp (H.grad i) 2 volume := by simpa using H.grad_memLp i
  apply le_of_forall_pos_le_add
  intro ε hε
  let c := 2/|h|
  have hc : 0≤c := div_nonneg (by norm_num) (abs_nonneg _)
  let δ := ε/(c+1)
  have hδ : 0<δ := div_pos hε (by linarith)
  obtain ⟨φ,hφ,h0,hg⟩ := compact_h1_approximation isOpen_univ H hs (subset_univ _) δ hδ
  have hφp : MemLp φ 2 volume := hφ.1.continuous.memLp_of_hasCompactSupport hφ.2.1
  have hφg : MemLp (Shared.partialDeriv φ i) 2 volume :=
    (test_partial hφ i).1.continuous.memLp_of_hasCompactSupport (test_partial hφ i).2.1
  have hfirst := l2Norm_le_sub_add (quotient_memLp hup i h) (quotient_memLp hφp i h)
  rw [← quotient_sub] at hfirst
  have hsecond := quotient_l2_coarse (hup.sub hφp) i h
  have hthird := smooth_quotient_l2_bound hφ.1 hφ.2.1 i h
  have hfourth := l2Norm_le_sub_add hφg hgp
  have he : l2Norm volume (Shared.partialDeriv φ i-H.grad i)=
      l2Norm volume (H.grad i-Shared.partialDeriv φ i) := by
    unfold l2Norm
    rw [eLpNorm_sub_comm]
  rw [he] at hfourth
  have hbound := mul_le_mul_of_nonneg_left h0.le hc
  have hid : c*δ+δ=ε := by dsimp [δ]; field_simp
  change l2Norm volume (diffQuot i h (u-φ))≤c*l2Norm volume (u-φ) at hsecond
  linarith [hg i]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CompactQuotientBound

-- BEGIN COMPLETE MODULE BilinearL2Bound
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem abs_integral_coefficient_mul_le {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {a f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (ha : AEStronglyMeasurable a μ) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ᵐ x ∂μ, |a x| ≤ M) :
    |∫ x, a x * f x * g x ∂μ| ≤ M * l2Norm μ f * l2Norm μ g := by
  exact (abs_integral_mul_le_l2 (memLp_mul_of_bound hf ha M hM hb) hg).trans
    (mul_le_mul_of_nonneg_right (l2Norm_mul_le hf M hM hb) (l2Norm_nonneg μ g))

theorem abs_sum_integral_coefficient_mul_le {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {n : ℕ} (a : Fin n → Fin n → E → ℝ)
    (f g : Fin n → E → ℝ) (hf : ∀ i, MemLp (f i) 2 μ)
    (hg : ∀ j, MemLp (g j) 2 μ) (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (M F G : ℝ) (hM : 0 ≤ M) (hF : 0 ≤ F)
    (hb : ∀ i j, ∀ᵐ x ∂μ, |a i j x| ≤ M)
    (hfN : ∀ i, l2Norm μ (f i) ≤ F) (hgN : ∀ j, l2Norm μ (g j) ≤ G) :
    |∑ i, ∑ j, ∫ x, a i j x * f i x * g j x ∂μ| ≤ (n : ℝ) ^ 2 * M * F * G := by
  have hb' (i j : Fin n) : |∫ x, a i j x * f i x * g j x ∂μ| ≤ M * F * G := by
    apply (abs_integral_coefficient_mul_le (hf i) (hg j) (ha i j) M hM (hb i j)).trans
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hfN i) hM) (hgN j)
      (l2Norm_nonneg μ (g j)) (mul_nonneg hM hF)
  calc
    _ ≤ ∑ i, |∑ j, ∫ x, a i j x * f i x * g j x ∂μ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, |∫ x, a i j x * f i x * g j x ∂μ| :=
      Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, M * F * G :=
      Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hb' i j))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, pow_two]; ring

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE BilinearL2Bound

-- BEGIN COMPLETE MODULE QuotientEnergyIdentity
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem quotient_bilinear_identity {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {n : ℕ} (b c : Fin n → Fin n → E → ℝ) (g G d : Fin n → E → ℝ)
    (η z : E → ℝ)
    (h0 : ∀ i j, Integrable (fun x => b i j x * (η x * G i x) * (η x * G j x)) μ)
    (h1 : ∀ i j, Integrable (fun x => (η x * c i j x) * g i x * (η x * G j x)) μ)
    (h2 : ∀ i j, Integrable (fun x => (b i j x * d j x) * (η x * G i x) * z x) μ)
    (h3 : ∀ i j, Integrable (fun x => (η x * c i j x * d j x) * g i x * z x) μ) :
    (∑ i, ∑ j, ∫ x, (b i j x * G i x + c i j x * g i x) *
      (η x ^ 2 * G j x + 2 * η x * d j x * z x) ∂μ) =
      (∑ i, ∑ j, ∫ x, b i j x * (η x * G i x) * (η x * G j x) ∂μ) +
      (∑ i, ∑ j, ∫ x, (η x * c i j x) * g i x * (η x * G j x) ∂μ) +
      2 * (∑ i, ∑ j, ∫ x, (b i j x * d j x) * (η x * G i x) * z x ∂μ) +
      2 * (∑ i, ∑ j, ∫ x, (η x * c i j x * d j x) * g i x * z x ∂μ) := by
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have h01 : Integrable (fun x =>
      b i j x * (η x * G i x) * (η x * G j x) +
      (η x * c i j x) * g i x * (η x * G j x)) μ := (h0 i j).add (h1 i j)
  have h2' : Integrable (fun x => 2 * ((b i j x * d j x) *
      (η x * G i x) * z x)) μ := (h2 i j).const_mul 2
  have h3' : Integrable (fun x => 2 * ((η x * c i j x * d j x) *
      g i x * z x)) μ := (h3 i j).const_mul 2
  have h012 : Integrable (fun x =>
      (b i j x * (η x * G i x) * (η x * G j x) +
      (η x * c i j x) * g i x * (η x * G j x)) +
      2 * ((b i j x * d j x) * (η x * G i x) * z x)) μ := h01.add h2'
  rw [← integral_const_mul, ← integral_const_mul]
  rw [← integral_add (h0 i j) (h1 i j)]
  rw [← integral_add h01 h2']
  rw [← integral_add h012 h3']
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem quotient_energy_absorption {θ K L X F Y : ℝ}
    (hθ : 0 < θ) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hX : 0 ≤ X) (hF : 0 ≤ F) (hY : 0 ≤ Y)
    (h : θ * X ^ 2 ≤ (F + K * Y) * X + L * (F + Y) ^ 2) :
    X ≤ (2 * (1 + K + L) / θ + 1) * (F + Y) := by
  apply energy_absorption hθ (by positivity) hX (by positivity)
  have h1 : (F + K * Y) * X ≤ (1 + K + L) * (F + Y) * X := by
    apply mul_le_mul_of_nonneg_right _ hX
    nlinarith [mul_nonneg hK hF, mul_nonneg hL hF, mul_nonneg hL hY]
  have h2 : L * (F + Y) ^ 2 ≤ (1 + K + L) * (F + Y) ^ 2 :=
    mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  linarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE QuotientEnergyIdentity

-- BEGIN COMPLETE MODULE QuotientEnergyCore
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem quotient_energy_core {E : Type*} [MeasurableSpace E] {μ : Measure E} {n : ℕ}
    (v g : Fin n → E → ℝ) (z f R : E → ℝ)
    (c1 c2 c3 : Fin n → Fin n → E → ℝ)
    (hv : ∀ i, MemLp (v i) 2 μ) (hg : ∀ i, MemLp (g i) 2 μ)
    (hz : MemLp z 2 μ) (hf : MemLp f 2 μ) (hR : MemLp R 2 μ)
    (hc1 : ∀ i j, AEStronglyMeasurable (c1 i j) μ)
    (hc2 : ∀ i j, AEStronglyMeasurable (c2 i j) μ)
    (hc3 : ∀ i j, AEStronglyMeasurable (c3 i j) μ)
    (A M D Y θ Q : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hD : 0 ≤ D)
    (hY : 0 ≤ Y) (hθ : 0 < θ)
    (hb1 : ∀ i j, ∀ᵐ x ∂μ, |c1 i j x| ≤ A)
    (hb2 : ∀ i j, ∀ᵐ x ∂μ, |c2 i j x| ≤ M * D)
    (hb3 : ∀ i j, ∀ᵐ x ∂μ, |c3 i j x| ≤ A * D)
    (hgN : ∀ i, l2Norm μ (g i) ≤ Y) (hzN : l2Norm μ z ≤ Y)
    (hRN : l2Norm μ R ≤ gradientL2 μ v + 2 * D * Y)
    (hprincipal : θ * gradientL2 μ v ^ 2 ≤ Q)
    (hid : Q + (∑ i, ∑ j, ∫ x, c1 i j x * g i x * v j x ∂μ) +
      2 * (∑ i, ∑ j, ∫ x, c2 i j x * v i x * z x ∂μ) +
      2 * (∑ i, ∑ j, ∫ x, c3 i j x * g i x * z x ∂μ) = -(∫ x, f x * R x ∂μ)) :
    gradientL2 μ v ≤
      (2 * (1 + ((n : ℝ) ^ 2 * A + 2 * n ^ 2 * M * D) +
        (2 * D + 2 * n ^ 2 * A * D)) / θ + 1) * (l2Norm μ f + Y) := by
  let X := gradientL2 μ v
  let F := l2Norm μ f
  let K : ℝ := (n : ℝ) ^ 2 * A + 2 * n ^ 2 * M * D
  let L : ℝ := 2 * D + 2 * n ^ 2 * A * D
  have hx : 0 ≤ X := gradientL2_nonneg μ v
  have hF : 0 ≤ F := l2Norm_nonneg μ f
  have h1 := abs_sum_integral_coefficient_mul_le c1 g v hg hv hc1 A Y X hA hY
    hb1 hgN (l2Norm_le_gradientL2 μ v)
  have h2 := abs_sum_integral_coefficient_mul_le c2 v (fun _ => z) hv (fun _ => hz)
    hc2 (M * D) X Y (mul_nonneg hM hD) hx hb2 (l2Norm_le_gradientL2 μ v) (fun _ => hzN)
  have h3 := abs_sum_integral_coefficient_mul_le c3 g (fun _ => z) hg (fun _ => hz)
    hc3 (A * D) Y Y (mul_nonneg hA hD) hY hb3 hgN (fun _ => hzN)
  have hr : |∫ x, f x * R x ∂μ| ≤ F * (X + 2 * D * Y) :=
    (abs_integral_mul_le_l2 hf hR).trans (mul_le_mul_of_nonneg_left hRN hF)
  have hraw : θ * X ^ 2 ≤ (F + K * Y) * X + 2 * D * F * Y +
      2 * (n : ℝ) ^ 2 * A * D * Y ^ 2 := by
    have hn1 := neg_le_abs (∑ i, ∑ j, ∫ x, c1 i j x * g i x * v j x ∂μ)
    have hn2 := neg_le_abs (∑ i, ∑ j, ∫ x, c2 i j x * v i x * z x ∂μ)
    have hn3 := neg_le_abs (∑ i, ∑ j, ∫ x, c3 i j x * g i x * z x ∂μ)
    have hnr := neg_le_abs (∫ x, f x * R x ∂μ)
    dsimp [K]
    nlinarith
  have hFY : F * Y ≤ (F + Y) ^ 2 := by nlinarith [mul_nonneg hF hY, sq_nonneg F, sq_nonneg Y]
  have hYY : Y ^ 2 ≤ (F + Y) ^ 2 := by nlinarith [mul_nonneg hF hY, sq_nonneg F]
  have hfirst := mul_le_mul_of_nonneg_left hFY (show 0 ≤ 2 * D by positivity)
  have hsecond := mul_le_mul_of_nonneg_left hYY
    (show 0 ≤ 2 * (n : ℝ) ^ 2 * A * D by positivity)
  apply quotient_energy_absorption hθ (show 0 ≤ K by dsimp [K]; positivity)
    (show 0 ≤ L by dsimp [L]; positivity) hx hF hY
  dsimp [L] at *
  nlinarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE QuotientEnergyCore

-- BEGIN COMPLETE MODULE CutoffQuotientEnergy
section

open MeasureTheory
namespace HunterPDE.Regularity.Proof

theorem cutoff_quotient_energy {E : Type*} [MeasurableSpace E] {μ : Measure E} {n : ℕ}
    (b c : Fin n → Fin n → E → ℝ) (g G d : Fin n → E → ℝ) (η z f R : E → ℝ)
    (hg : ∀ i, MemLp (g i) 2 μ) (hG : ∀ i, MemLp (G i) 2 μ)
    (hz : MemLp z 2 μ) (hf : MemLp f 2 μ) (hR : MemLp R 2 μ)
    (hb : ∀ i j, AEStronglyMeasurable (b i j) μ)
    (hc : ∀ i j, AEStronglyMeasurable (c i j) μ)
    (hd : ∀ j, AEStronglyMeasurable (d j) μ) (hη : AEStronglyMeasurable η μ)
    (A M D Y θ : ℝ) (hA : 0 ≤ A) (hM : 0 ≤ M) (hD : 0 ≤ D) (hY : 0 ≤ Y) (hθ : 0 < θ)
    (hbB : ∀ i j, ∀ᵐ x ∂μ, |b i j x| ≤ M)
    (hcB : ∀ i j, ∀ᵐ x ∂μ, |c i j x| ≤ A)
    (hdB : ∀ j, ∀ᵐ x ∂μ, |d j x| ≤ D) (hηB : ∀ᵐ x ∂μ, |η x| ≤ 1)
    (hgN : ∀ i, l2Norm μ (g i) ≤ Y) (hzN : l2Norm μ z ≤ Y)
    (hRN : l2Norm μ R ≤ gradientL2 μ (fun i x => η x * G i x) + 2 * D * Y)
    (hprincipal : θ * gradientL2 μ (fun i x => η x * G i x) ^ 2 ≤
      ∑ i, ∑ j, ∫ x, b i j x * (η x * G i x) * (η x * G j x) ∂μ)
    (hid : (∑ i, ∑ j, ∫ x, (b i j x * G i x + c i j x * g i x) *
      (η x ^ 2 * G j x + 2 * η x * d j x * z x) ∂μ) = -(∫ x, f x * R x ∂μ)) :
    gradientL2 μ (fun i x => η x * G i x) ≤
      (2 * (1 + ((n : ℝ) ^ 2 * A + 2 * n ^ 2 * M * D) +
        (2 * D + 2 * n ^ 2 * A * D)) / θ + 1) * (l2Norm μ f + Y) := by
  let v : Fin n → E → ℝ := fun i x => η x * G i x
  have hv i : MemLp (v i) 2 μ := memLp_mul_of_bound (hG i) hη 1 zero_le_one hηB
  have hec i j : ∀ᵐ x ∂μ, |η x * c i j x| ≤ A := by
    filter_upwards [hηB,hcB i j] with x hx hy
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul A)
  have hbd i j : ∀ᵐ x ∂μ, |b i j x * d j x| ≤ M * D := by
    filter_upwards [hbB i j,hdB j] with x hx hy
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hM
  have hecd i j : ∀ᵐ x ∂μ, |η x * c i j x * d j x| ≤ A * D := by
    filter_upwards [hec i j,hdB j] with x hx hy
    rw [abs_mul]
    exact mul_le_mul hx hy (abs_nonneg _) hA
  have h0 i j : Integrable (fun x => b i j x * (η x * G i x) * (η x * G j x)) μ :=
    coefficient_product_integrable (hv i) (hv j) (hb i j) M (hbB i j)
  have h1 i j : Integrable (fun x => (η x * c i j x) * g i x * (η x * G j x)) μ :=
    coefficient_product_integrable (hg i) (hv j) (hη.mul (hc i j)) A (hec i j)
  have h2 i j : Integrable (fun x => (b i j x * d j x) * (η x * G i x) * z x) μ :=
    coefficient_product_integrable (hv i) hz ((hb i j).mul (hd j)) (M*D) (hbd i j)
  have h3 i j : Integrable (fun x => (η x * c i j x * d j x) * g i x * z x) μ :=
    coefficient_product_integrable (hg i) hz ((hη.mul (hc i j)).mul (hd j)) (A*D) (hecd i j)
  rw [quotient_bilinear_identity b c g G d η z h0 h1 h2 h3] at hid
  exact quotient_energy_core v g z f R
    (fun i j x => η x * c i j x) (fun i j x => b i j x * d j x)
    (fun i j x => η x * c i j x * d j x)
    hv hg hz hf hR (fun i j => hη.mul (hc i j))
    (fun i j => (hb i j).mul (hd j)) (fun i j => (hη.mul (hc i j)).mul (hd j))
    A M D Y θ _ hA hM hD hY hθ hec hbd hecd hgN hzN hRN hprincipal hid

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CutoffQuotientEnergy

-- BEGIN COMPLETE MODULE FluxQuotient
section

open Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma diffQuot_mul (a g : E → ℝ) (i : Fin n) (h : ℝ) (x : E) :
    diffQuot i h (fun y => a y * g y) x =
      a (x + h • EuclideanSpace.single i 1) * diffQuot i h g x +
        diffQuot i h a x * g x := by
  unfold diffQuot
  ring

lemma indicator_flux_quotient {Ω K : Set E} (a g G : E → ℝ)
    (i : Fin n) (h : ℝ) (hΩ : K ⊆ Ω)
    (hshift : ∀ x ∈ K, x + h • EuclideanSpace.single i 1 ∈ Ω)
    (hG : ∀ x ∈ K, G x = g x)
    (hGs : ∀ x ∈ K, G (x + h • EuclideanSpace.single i 1) =
      g (x + h • EuclideanSpace.single i 1)) :
    ∀ x ∈ K, diffQuot i h (Ω.indicator (fun y => a y * g y)) x =
      a (x + h • EuclideanSpace.single i 1) * diffQuot i h G x +
        diffQuot i h a x * G x := by
  intro x hx
  unfold diffQuot
  rw [indicator_of_mem (hΩ hx), indicator_of_mem (hshift x hx), hG x hx, hGs x hx]
  ring

lemma indicator_flux_pair {Ω K : Set E} (a g G W : E → ℝ)
    (i : Fin n) (h : ℝ) (hΩ : K ⊆ Ω)
    (hshift : ∀ x ∈ K, x + h • EuclideanSpace.single i 1 ∈ Ω)
    (hG : ∀ x ∈ K, G x = g x)
    (hGs : ∀ x ∈ K, G (x + h • EuclideanSpace.single i 1) =
      g (x + h • EuclideanSpace.single i 1))
    (hW : Function.support W ⊆ K) (x : E) :
    diffQuot i h (Ω.indicator (fun y => a y * g y)) x * W x =
      (K.indicator (fun y => a (y + h • EuclideanSpace.single i 1)) x * diffQuot i h G x +
        K.indicator (diffQuot i h a) x * G x) * W x := by
  by_cases hx : x ∈ K
  · rw [indicator_flux_quotient a g G i h hΩ hshift hG hGs x hx,
      indicator_of_mem hx, indicator_of_mem hx]
  · have hw : W x = 0 := by by_contra hh; exact hx (hW hh)
    simp [hw]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE FluxQuotient

-- BEGIN COMPLETE MODULE LocalizedCoefficients
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma localized_coefficient_measurable {Ω K : Set E} (hK : MeasurableSet K)
    (a : E → ℝ) (ha : ContinuousOn a Ω) (hKΩ : K ⊆ Ω)
    (i : Fin n) (h : ℝ) (hshift : ∀ x ∈ K, x + h • EuclideanSpace.single i 1 ∈ Ω) :
    AEStronglyMeasurable (K.indicator (fun x => a (x + h • EuclideanSpace.single i 1))) volume ∧
    AEStronglyMeasurable (K.indicator (diffQuot i h a)) volume := by
  have hc : ContinuousOn (fun x => a (x + h • EuclideanSpace.single i 1)) K :=
    ha.comp (continuous_id.add continuous_const).continuousOn hshift
  constructor
  · exact (aestronglyMeasurable_indicator_iff hK).mpr (hc.aestronglyMeasurable hK)
  · apply (aestronglyMeasurable_indicator_iff hK).mpr
    apply ContinuousOn.aestronglyMeasurable _ hK
    exact (hc.sub (ha.mono hKΩ)).div_const h

lemma indicator_abs_bound {K : Set E} {a : E → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (ha : ∀ x ∈ K, |a x| ≤ M) : ∀ x, |K.indicator a x| ≤ M := by
  intro x
  by_cases hx : x ∈ K
  · simpa [hx] using ha x hx
  · simpa [hx] using hM

lemma partial_support_subset (η : E → ℝ) (i : Fin n) :
    Function.support (Shared.partialDeriv η i) ⊆ tsupport η :=
  (subset_tsupport _).trans (tsupport_fderiv_apply_subset ℝ _)

lemma squared_cutoff_gradient_support (η z : E → ℝ) (G : Fin n → E → ℝ) (i : Fin n) :
    Function.support (fun x => η x ^ 2 * G i x + 2 * η x * Shared.partialDeriv η i x * z x)
      ⊆ tsupport η := by
  intro x hx
  by_contra hs
  have hz := image_eq_zero_of_notMem_tsupport hs
  simp [hz] at hx

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE LocalizedCoefficients

-- BEGIN COMPLETE MODULE ShiftedEllipticity
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma ae_restrict_shift {Ω : Set E} (hΩ : MeasurableSet Ω) {P : E → Prop}
    (hP : ∀ᵐ x ∂volume.restrict Ω, P x) (z : E) :
    ∀ᵐ x ∂volume, x + z ∈ Ω → P (x + z) := by
  have hg : ∀ᵐ x ∂volume, x ∈ Ω → P x := (ae_restrict_iff' hΩ).mp hP
  exact (measurePreserving_add_right volume z).quasiMeasurePreserving.ae hg

lemma shifted_ellipticity_cutoff {Ω : Set E} (hΩ : MeasurableSet Ω)
    (a : Fin n → Fin n → E → ℝ) (θ : ℝ)
    (hell : UniformlyElliptic Ω a θ) (η : E → ℝ) (G : Fin n → E → ℝ) (z : E)
    (hshift : ∀ x, η x ≠ 0 → x + z ∈ Ω) :
    ∀ᵐ x ∂volume,
      θ * ∑ i, (η x * G i x) ^ 2 ≤
        ∑ i, ∑ j, a i j (x + z) * (η x * G i x) * (η x * G j x) := by
  filter_upwards [ae_restrict_shift hΩ hell.2 z] with x hx
  by_cases hz : η x = 0
  · simp [hz]
  · exact hx (hshift x hz) (fun i => η x * G i x)

lemma cutoff_elliptic_integral {Ω : Set E} (hΩ : MeasurableSet Ω)
    (a : Fin n → Fin n → E → ℝ) (θ : ℝ)
    (hell : UniformlyElliptic Ω a θ) (η : E → ℝ) (G : Fin n → E → ℝ) (z : E)
    (hshift : ∀ x, η x ≠ 0 → x + z ∈ Ω)
    (hg : ∀ i, MemLp (fun x => η x * G i x) 2 volume)
    (hint : ∀ i j, Integrable
      (fun x => a i j (x + z) * (η x * G i x) * (η x * G j x)) volume) :
    θ * ∑ i, l2Norm volume (fun x => η x * G i x) ^ 2 ≤
      ∑ i, ∑ j, ∫ x, a i j (x + z) * (η x * G i x) * (η x * G j x) := by
  have hi (i : Fin n) : Integrable (fun x => (η x * G i x) ^ 2) volume := by
    have h : Integrable (fun x => (η x * G i x) * (η x * G i x)) volume :=
      (hg i).integrable_mul (hg i)
    simpa only [pow_two] using h
  have hs := integral_mono_ae ((integrable_finsetSum _ (fun i _ => hi i)).const_mul θ)
    (integrable_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j)))
    (shifted_ellipticity_cutoff hΩ a θ hell η G z hshift)
  rw [integral_const_mul, integral_finsetSum _ (fun i _ => hi i)] at hs
  simp_rw [integral_sq_eq_l2_sq (hg _)] at hs
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))] at hs
  simp_rw [integral_finsetSum _ (fun j _ => hint _ j)] at hs
  exact hs

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE ShiftedEllipticity

-- BEGIN COMPLETE MODULE NativeQuotientEstimate
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

theorem native_quotient_estimate {Ω : Set E} (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → E → ℝ) (f u u0 η : E → ℝ)
    (U : H1Data Ω u) (J : H1Data univ u0)
    (hsol : IsWeakSolution Ω a f u) (hf : MemLp f 2 (volume.restrict Ω))
    (ha : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (hac : ∀ i j, ContinuousOn (a i j) Ω)
    (hs : HasCompactSupport u0) (hη : Shared.IsTestFunction Ω η)
    (hηB : ∀ x, |η x| ≤ 1) (k : Fin n) (h : ℝ)
    (hshift : ∀ x ∈ tsupport η, x + h • EuclideanSpace.single k 1 ∈ Ω)
    (hmatch : ∀ i x, x ∈ tsupport η → J.grad i x = U.grad i x)
    (hmatchs : ∀ i x, x ∈ tsupport η → J.grad i (x + h • EuclideanSpace.single k 1) =
      U.grad i (x + h • EuclideanSpace.single k 1))
    (M D Y θ : ℝ) (hM : 0 ≤ M) (hD : 0 ≤ D) (hY : 0 ≤ Y)
    (hell : UniformlyElliptic Ω a θ)
    (haB : ∀ i j x, x ∈ tsupport η → |a i j (x + h • EuclideanSpace.single k 1)| ≤ M)
    (haQ : ∀ i j x, x ∈ tsupport η → |diffQuot k h (a i j) x| ≤ M)
    (hdB : ∀ j, ∀ᵐ x ∂volume, |Shared.partialDeriv η j x| ≤ D)
    (hgN : ∀ i, l2Norm volume (J.grad i) ≤ Y)
    (hRN : l2Norm volume (diffQuot k (-h) (fun x => η x ^ 2 * diffQuot k h u0 x)) ≤
      gradientL2 volume (fun i x => η x * diffQuot k h (J.grad i) x) + 2 * D * Y) :
    gradientL2 volume (fun i x => η x * diffQuot k h (J.grad i) x) ≤
      (2 * (1 + ((n : ℝ) ^ 2 * M + 2 * n ^ 2 * M * D) +
        (2 * D + 2 * n ^ 2 * M * D)) / θ + 1) * (l2Norm (volume.restrict Ω) f + Y) := by
  let K := tsupport η
  let b : Fin n → Fin n → E → ℝ := fun i j => K.indicator (fun x => a i j (x + h • EuclideanSpace.single k 1))
  let c : Fin n → Fin n → E → ℝ := fun i j => K.indicator (diffQuot k h (a i j))
  let G : Fin n → E → ℝ := fun i => diffQuot k h (J.grad i)
  let z := diffQuot k h u0
  let w : E → ℝ := fun x => η x ^ 2 * z x
  let R := diffQuot k (-h) w
  let W := J.differenceCutoff hη k h
  let V := (W.backwardTestExplicit k h).restrict (subset_univ Ω)
  have hg i : MemLp (J.grad i) 2 volume := by simpa using J.grad_memLp i
  have hG i : MemLp (G i) 2 volume := quotient_memLp (hg i) k h
  have hu0 : MemLp u0 2 volume := by simpa using J.self_memLp
  have hz : MemLp z 2 volume := quotient_memLp hu0 k h
  have hw : MemLp w 2 volume := by simpa using W.self_memLp
  have hR : MemLp R 2 volume := quotient_memLp hw k (-h)
  have hfp : MemLp (Ω.indicator f) 2 volume := (memLp_indicator_iff_restrict hΩ.measurableSet).mpr hf
  have hbc i j := localized_coefficient_measurable (isClosed_tsupport η).measurableSet
    (a i j) (hac i j) hη.2.2 k h hshift
  have hbB i j : ∀ᵐ x ∂volume, |b i j x| ≤ M :=
    Filter.Eventually.of_forall (indicator_abs_bound hM (haB i j))
  have hcB i j : ∀ᵐ x ∂volume, |c i j x| ≤ M :=
    Filter.Eventually.of_forall (indicator_abs_bound hM (haQ i j))
  have hηm : AEStronglyMeasurable η volume := hη.1.continuous.aestronglyMeasurable
  have hηb : ∀ᵐ x ∂volume, |η x| ≤ 1 := Filter.Eventually.of_forall hηB
  have hv i : MemLp (fun x => η x * G i x) 2 volume :=
    memLp_mul_of_bound (hG i) hηm 1 zero_le_one hηb
  have hflux i j : MemLp (fun x => a i j x * U.grad i x) 2 (volume.restrict Ω) := by
    have hp : MemLp (fun x => U.grad i x * a i j x) 2 (volume.restrict Ω) :=
      (ha i j).mul' (U.grad_memLp i)
    convert hp using 1
    ext x
    ring
  have hid := discrete_weak_identity hΩ a f u w (fun x => -R x) U W V hsol
    (difference_test_memW0 J hΩ hη k h hshift) hflux k h (fun _ => rfl) (fun _ _ => rfl)
  have hpair i j x : diffQuot k h (Ω.indicator (fun y => a i j y * U.grad i y)) x * W.grad j x =
      (b i j x * G i x + c i j x * J.grad i x) * W.grad j x :=
    indicator_flux_pair (a i j) (U.grad i) (J.grad i) (W.grad j) k h hη.2.2 hshift
      (hmatch i) (hmatchs i) (squared_cutoff_gradient_support η z G j) x
  simp_rw [hpair] at hid
  have hwg (j : Fin n) (x : E) : W.grad j x =
      η x ^ 2 * G j x + 2 * η x * Shared.partialDeriv η j x * z x := rfl
  simp_rw [hwg] at hid
  rw [← indicator_pair_integral hΩ.measurableSet f R] at hid
  have hint i j : Integrable (fun x => b i j x * (η x * G i x) * (η x * G j x)) volume :=
    coefficient_product_integrable (hv i) (hv j) (hbc i j).1 M (hbB i j)
  have heq i j : (fun x => a i j (x + h • EuclideanSpace.single k 1) * (η x * G i x) * (η x * G j x)) =
      (fun x => b i j x * (η x * G i x) * (η x * G j x)) := by
    funext x
    by_cases hx : x ∈ K
    · simp [b,hx]
    · have hzη : η x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hzη]
  have hprincipal := cutoff_elliptic_integral hΩ.measurableSet a θ hell η G
    (h • EuclideanSpace.single k 1) (fun x hx => hshift x (subset_tsupport η hx)) hv
    (fun i j => (heq i j).symm ▸ hint i j)
  simp_rw [heq] at hprincipal
  rw [← gradientL2_sq volume (fun i x => η x * G i x)] at hprincipal
  have he := cutoff_quotient_energy b c J.grad G (Shared.partialDeriv η) η z (Ω.indicator f) R
    hg hG hz hfp hR (fun i j => (hbc i j).1) (fun i j => (hbc i j).2)
    (fun j => (test_partial hη j).1.continuous.aestronglyMeasurable) hηm
    M M D Y θ hM hM hD hY hell.1 hbB hcB hdB hηb hgN
    ((compact_quotient_l2_bound J hs k h).trans (hgN k)) hRN hprincipal hid
  simpa only [l2Norm, eLpNorm_indicator_eq_eLpNorm_restrict hΩ.measurableSet] using he

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE NativeQuotientEstimate

-- BEGIN COMPLETE MODULE DifferenceTestNorm
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma difference_test_norm {u η : E → ℝ} (H : H1Data univ u)
    (hη : Shared.IsTestFunction Ω η) (k : Fin n) (h D Y : ℝ) (hD : 0≤D)
    (hηB : ∀ᵐ x ∂volume,|η x|≤1) (hdB : ∀ᵐ x ∂volume,|Shared.partialDeriv η k x|≤D)
    (hY : l2Norm volume (H.grad k)≤Y) (hu : HasCompactSupport u) :
    l2Norm volume (diffQuot k (-h) (fun x => η x^2*diffQuot k h u x)) ≤
      gradientL2 volume (fun j x => η x*diffQuot k h (H.grad j) x)+2*D*Y := by
  let z := diffQuot k h u
  let G := fun j => diffQuot k h (H.grad j)
  have hup : MemLp u 2 volume := by simpa using H.self_memLp
  have hgp (j : Fin n) : MemLp (H.grad j) 2 volume := by simpa using H.grad_memLp j
  have hz : MemLp z 2 volume := quotient_memLp hup k h
  have hG (j : Fin n) : MemLp (G j) 2 volume := quotient_memLp (hgp j) k h
  have hηm := hη.1.continuous.aestronglyMeasurable (μ := volume)
  have hηae := hηB
  have hv : MemLp (fun x => η x*G k x) 2 volume := memLp_mul_of_bound (hG k) hηm 1 zero_le_one hηae
  have hdd := (test_partial hη k).1.continuous.aestronglyMeasurable (μ := volume)
  have hd : ∀ᵐ x ∂volume,|η x*Shared.partialDeriv η k x|≤D := by
    filter_upwards [hηB,hdB] with x hx hy
    rw [abs_mul]
    exact (mul_le_mul hx hy (abs_nonneg _) zero_le_one).trans_eq (one_mul D)
  have hz2 := memLp_mul_of_bound hz (hηm.mul hdd) D hD hd
  have hv2 := memLp_mul_of_bound hv hηm 1 zero_le_one hηae
  have hb := compact_quotient_l2_bound (H.differenceCutoff hη k h)
    (squaredCutoff_support hη.2.1).1 k (-h)
  have hgrad : (H.differenceCutoff hη k h).grad k =
      (fun x => η x*(η x*G k x))+(fun x => 2*((η x*Shared.partialDeriv η k x)*z x)) := by
    ext x; rw [differenceCutoff_grad]; dsimp [G,z]; ring
  rw [hgrad] at hb
  have ha := l2Norm_add_le hv2 (hz2.const_mul 2)
  have hfirst := l2Norm_mul_le hv 1 zero_le_one hηae
  simp only [one_mul] at hfirst
  have hsecond := l2Norm_mul_le hz D hD hd
  have hzz := (compact_quotient_l2_bound H hu k h).trans hY
  rw [l2Norm_const_mul 2 hz2] at ha
  norm_num only [show |(2:ℝ)|=2 by norm_num] at ha
  simp only [Pi.mul_apply] at ha
  have hGG := l2Norm_le_gradientL2 volume (fun j x => η x*G j x) k
  have hDY := mul_le_mul_of_nonneg_left hzz hD
  change l2Norm volume z≤Y at hzz
  dsimp [G] at hGG
  dsimp [G,z] at hb ha hfirst hsecond hDY ⊢
  linarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE DifferenceTestNorm

-- BEGIN COMPLETE MODULE CutoffLocality
section

open Set Filter
open scoped Topology
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma partial_eq_zero_on_constant {U : Set E} (hU : IsOpen U) {η : E → ℝ} {c : ℝ}
    (hc : ∀ x ∈ U, η x = c) {x : E} (hx : x ∈ U) (i : Fin n) :
    Shared.partialDeriv η i x = 0 := by
  have he : η =ᶠ[𝓝 x] (fun _ => c) :=
    Filter.Eventually.mono (hU.mem_nhds hx) (fun y hy => hc y hy)
  unfold Shared.partialDeriv
  rw [he.fderiv_eq]
  simp

lemma cutoff_local_value {U : Set E} {u χ : E → ℝ}
    (hχ : ∀ x ∈ U, χ x = 1) : EqOn (fun x => u x * χ x) u U := by
  intro x hx
  simp [hχ x hx]

lemma cutoff_local_gradient {Ω U : Set E} {u χ : E → ℝ} (H : H1Data Ω u)
    (hΩ : IsOpen Ω) (hχ : Shared.IsTestFunction Ω χ)
    (hU : IsOpen U) (hone : ∀ x ∈ U, χ x = 1) (i : Fin n) :
    EqOn ((H.cutoff hΩ hχ).grad i) (H.grad i) U := by
  intro x hx
  change H.grad i x * χ x + u x * Shared.partialDeriv χ i x = _
  rw [hone x hx, partial_eq_zero_on_constant hU hone hx i]
  ring

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CutoffLocality

-- BEGIN COMPLETE MODULE LocalDifferenceBound
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma local_quotient_gradient_bound {Ω' : Set E} (hΩ' : MeasurableSet Ω')
    (g : Fin n → E → ℝ) (η : E → ℝ) (i k : Fin n) (h : ℝ)
    (hg : ∀ j, MemLp (g j) 2 volume)
    (hη : AEStronglyMeasurable η volume) (hηB : ∀ᵐ x ∂volume, |η x| ≤ 1)
    (hone : ∀ x ∈ Ω', η x = 1) :
    l2Norm (volume.restrict Ω') (diffQuot k h (g i)) ≤
      gradientL2 volume (fun j x => η x * diffQuot k h (g j) x) := by
  have hp j := memLp_mul_of_bound (quotient_memLp (hg j) k h) hη 1 zero_le_one hηB
  calc
    _ = l2Norm (volume.restrict Ω') (fun x => η x * diffQuot k h (g i) x) := by
      apply l2Norm_restrict_eqOn hΩ'
      intro x hx
      simp [hone x hx]
    _ ≤ l2Norm volume (fun x => η x * diffQuot k h (g i) x) :=
      l2Norm_mono_measure (hp i) Measure.restrict_le_self
    _ ≤ _ := l2Norm_le_gradientL2 volume (fun j x => η x * diffQuot k h (g j) x) i

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE LocalDifferenceBound

-- BEGIN COMPLETE MODULE InteriorQuotientBound
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

noncomputable def InteriorSetup.quotientConstant {Ω Ω' : Set E}
    {a : Fin n → Fin n → E → ℝ} (S : InteriorSetup Ω Ω' a) (θ : ℝ) : ℝ :=
  (2 * (1 + ((n : ℝ) ^ 2 * S.M + 2 * n ^ 2 * S.M * S.D) +
    (2 * S.D + 2 * n ^ 2 * S.M * S.D)) / θ + 1) * (1 + S.C)

lemma InteriorSetup.quotientConstant_pos {Ω Ω' : Set E}
    {a : Fin n → Fin n → E → ℝ} (S : InteriorSetup Ω Ω' a) {θ : ℝ} (hθ : 0 < θ) :
    0 < S.quotientConstant θ := by
  have := S.M_pos
  have := S.D_pos
  have := S.C_pos
  unfold InteriorSetup.quotientConstant
  positivity

 theorem InteriorSetup.quotient_bound {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (hΩ' : MeasurableSet Ω') {a : Fin n → Fin n → E → ℝ} (S : InteriorSetup Ω Ω' a)
    (ha : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (hac : ∀ i j, ContinuousOn (a i j) Ω) {θ : ℝ} (hell : UniformlyElliptic Ω a θ)
    (f u : E → ℝ) (U : H1Data Ω u) (hsol : IsWeakSolution Ω a f u)
    (hf : MemLp f 2 (volume.restrict Ω)) (i k : Fin n) (h : ℝ)
    (hh : h ≠ 0) (hsmall : |h| ≤ S.ε) :
    l2Norm (volume.restrict Ω') (diffQuot k h ((U.cutoff hΩ S.χ_test).grad i)) ≤
      S.quotientConstant θ * (l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u) := by
  let J := U.cutoff hΩ S.χ_test
  let T := l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u
  let Y := S.C * T
  have hT : 0 ≤ T := add_nonneg (l2Norm_nonneg _ _) (l2Norm_nonneg _ _)
  have hY : 0 ≤ Y := mul_nonneg S.C_pos.le hT
  have hJ i : l2Norm volume (J.grad i) ≤ Y := S.gradient_bound f u U hΩ hsol hf i
  have hs : HasCompactSupport (fun x => u x * S.χ x) := S.χ_test.2.1.mul_left
  have hη : Shared.IsTestFunction Ω S.η :=
    ⟨S.η_test.1,S.η_test.2.1,S.η_test.2.2.trans S.inner_subset⟩
  have hshift x hx := S.inner_subset (S.shift_inner k h hsmall x hx)
  have hm (j : Fin n) (x : E) (hx : x ∈ tsupport S.η) := cutoff_local_gradient U hΩ S.χ_test S.inner_open S.χ_one j (S.η_test.2.2 hx)
  have hms (j : Fin n) (x : E) (hx : x ∈ tsupport S.η) := cutoff_local_gradient U hΩ S.χ_test S.inner_open S.χ_one j
    (S.shift_inner k h hsmall x hx)
  have hRN := difference_test_norm J hη k h S.D Y S.D_pos.le
    (Filter.Eventually.of_forall S.η_bound) (S.derivative_bound k) (hJ k) hs
  have hb := native_quotient_estimate hΩ a f u (fun x => u x * S.χ x) S.η U J hsol hf ha hac hs hη
    S.η_bound k h hshift hm hms S.M S.D Y θ S.M_pos.le S.D_pos.le hY hell
    (fun j l x hx => (S.coefficient_bounds k j l h hh hsmall x hx).1)
    (fun j l x hx => (S.coefficient_bounds k j l h hh hsmall x hx).2)
    S.derivative_bound hJ hRN
  have hl := local_quotient_gradient_bound hΩ' J.grad S.η i k h
    (fun j => by simpa using J.grad_memLp j) hη.1.continuous.aestronglyMeasurable
    (Filter.Eventually.of_forall S.η_bound) S.η_one
  apply (hl.trans hb).trans
  let B : ℝ := 2 * (1 + ((n : ℝ) ^ 2 * S.M + 2 * n ^ 2 * S.M * S.D) +
    (2 * S.D + 2 * n ^ 2 * S.M * S.D)) / θ + 1
  have hB : 0 ≤ B := by
    have := S.M_pos; have := S.D_pos; have := hell.1
    dsimp [B]; positivity
  change B * (l2Norm (volume.restrict Ω) f + Y) ≤ (B * (1 + S.C)) * T
  have huN := l2Norm_nonneg (volume.restrict Ω) u
  dsimp [Y,T]
  nlinarith

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE InteriorQuotientBound

-- BEGIN COMPLETE MODULE CutoffGradientCompact
section

open MeasureTheory Set
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

lemma cutoff_gradient_support {Ω : Set E} {u χ : E → ℝ} (H : H1Data Ω u)
    (hΩ : IsOpen Ω) (hχ : Shared.IsTestFunction Ω χ) (i : Fin n) :
    tsupport ((H.cutoff hΩ hχ).grad i) ⊆ tsupport χ := by
  apply closure_minimal _ (isClosed_tsupport χ)
  intro x hx
  by_contra hh
  have hz := image_eq_zero_of_notMem_tsupport hh
  have hp : Shared.partialDeriv χ i x = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    exact fun h => hh ((tsupport_fderiv_apply_subset ℝ _) h)
  change H.grad i x * χ x + u x * Shared.partialDeriv χ i x ≠ 0 at hx
  simp [hz,hp] at hx

lemma cutoff_gradient_integrable {Ω : Set E} {u χ : E → ℝ} (H : H1Data Ω u)
    (hΩ : IsOpen Ω) (hχ : Shared.IsTestFunction Ω χ) (i : Fin n) :
    Integrable ((H.cutoff hΩ hχ).grad i) volume := by
  apply integrable_of_memLp_compact (by simpa using (H.cutoff hΩ hχ).grad_memLp i)
  exact hχ.2.1.of_isClosed_subset (isClosed_tsupport _) (cutoff_gradient_support H hΩ hχ i)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE CutoffGradientCompact

-- BEGIN COMPLETE MODULE TestSpace
section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HunterPDE.Regularity.Proof

variable {n : ℕ}

/-- Smooth compactly supported tests, as an actual real vector space. -/
def testSpace (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    Submodule ℝ (EuclideanSpace ℝ (Fin n) → ℝ) where
  carrier := {φ | Shared.IsTestFunction Ω φ}
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  add_mem' := by
    intro f g hf hg
    exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
      (tsupport_add f g).trans (union_subset hf.2.2 hg.2.2)⟩
  smul_mem' := by
    intro c f hf
    exact ⟨contDiff_const.smul hf.1, hf.2.1.smul_left,
      (tsupport_smul_subset_right (fun _ => c) f).trans hf.2.2⟩

theorem test_memLp (Ω : Set (EuclideanSpace ℝ (Fin n))) (φ : testSpace Ω) :
    MemLp (φ : EuclideanSpace ℝ (Fin n) → ℝ) 2 (volume.restrict Ω) :=
  (φ.property.1.continuous.memLp_of_hasCompactSupport φ.property.2.1).restrict _

noncomputable def testToLp (Ω : Set (EuclideanSpace ℝ (Fin n))) :
    testSpace Ω →ₗ[ℝ] Lp ℝ 2 (volume.restrict Ω) where
  toFun φ := (test_memLp Ω φ).toLp φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem norm_testToLp (Ω : Set (EuclideanSpace ℝ (Fin n))) (φ : testSpace Ω) :
    ‖testToLp Ω φ‖ = (eLpNorm (φ : EuclideanSpace ℝ (Fin n) → ℝ) 2
      (volume.restrict Ω)).toReal := Lp.norm_toLp _ (test_memLp Ω φ)

noncomputable def testPartial (Ω : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n) :
    testSpace Ω →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) → ℝ) where
  toFun φ := Shared.partialDeriv φ i
  map_add' f g := by
    funext x
    simp only [Shared.partialDeriv, Submodule.coe_add, Pi.add_apply]
    rw [fderiv_add (f.property.1.differentiable (by simp)).differentiableAt
      (g.property.1.differentiable (by simp)).differentiableAt]
    rfl
  map_smul' c f := by
    funext x
    simp only [Shared.partialDeriv, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply]
    rw [fderiv_const_smul (f.property.1.differentiable (by simp)).differentiableAt]
    rfl

theorem testPartial_isTest (Ω : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n)
    (φ : testSpace Ω) : Shared.IsTestFunction Ω (testPartial Ω i φ) := by
  refine ⟨?_, φ.property.2.1.fderiv_apply ℝ _, ?_⟩
  · exact (φ.property.1.fderiv_right (by simp)).clm_apply contDiff_const
  · exact (tsupport_fderiv_apply_subset ℝ _).trans φ.property.2.2

theorem testPartial_memLp (Ω : Set (EuclideanSpace ℝ (Fin n))) (i : Fin n)
    (φ : testSpace Ω) : MemLp (testPartial Ω i φ) 2 (volume.restrict Ω) :=
  ((testPartial_isTest Ω i φ).1.continuous.memLp_of_hasCompactSupport
    (testPartial_isTest Ω i φ).2.1).restrict _

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE TestSpace

-- BEGIN COMPLETE MODULE TestQuotientLimit
section

open MeasureTheory Filter Set
open scoped Topology

namespace HunterPDE.Regularity.Proof

theorem test_backward_difference_limit {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (φ : testSpace Ω)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Integrable g volume) (i : Fin n) :
    Tendsto (fun t : ℝ => ∫ x, ((φ.val (x - t • EuclideanSpace.single i (1 : ℝ)) - φ.val x) / t) * g x)
      (𝓝[>] 0) (𝓝 (-∫ x, g x * Shared.partialDeriv φ.val i x)) := by
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport
    φ.property.2.1 φ.property.1 (by simp)
  have ht := hC.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hg
    (-EuclideanSpace.single i (1 : ℝ))
  have hder (x : EuclideanSpace ℝ (Fin n)) :
      lineDeriv ℝ φ.val x (-EuclideanSpace.single i (1 : ℝ)) =
        -Shared.partialDeriv φ.val i x := by
    rw [(φ.property.1.differentiable (by simp)).differentiableAt.lineDeriv_eq_fderiv]
    simp only [Shared.partialDeriv, map_neg]
  simp only [hder, neg_mul, integral_neg] at ht
  convert ht using 1
  · funext t
    apply integral_congr_ae
    filter_upwards with x
    simp only [smul_neg, sub_eq_add_neg, smul_eq_mul, div_eq_mul_inv]
    ring
  · congr 2
    apply integral_congr_ae
    filter_upwards with x
    exact mul_comm _ _

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE TestQuotientLimit

-- BEGIN COMPLETE MODULE TestDifferenceAdjoint
section

open MeasureTheory Filter
open scoped Topology

namespace HunterPDE.Regularity.Proof

theorem integral_difference_test_adjoint {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (φ : testSpace Ω)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Integrable g volume)
    (i : Fin n) (t : ℝ) :
    (∫ x, diffQuot i t g x * φ.val x) =
      ∫ x, ((φ.val (x - t • EuclideanSpace.single i (1 : ℝ)) - φ.val x) / t) * g x := by
  let e := t • EuclideanSpace.single i (1 : ℝ)
  obtain ⟨B, hB⟩ := φ.property.2.1.exists_bound_of_continuous φ.property.1.continuous
  have h0 : Integrable (fun x => g x * φ.val x) volume :=
    hg.mul_bdd φ.property.1.continuous.aestronglyMeasurable (Filter.Eventually.of_forall hB)
  have hm : Integrable (fun x => g x * φ.val (x - e)) volume := by
    apply hg.mul_bdd (φ.property.1.continuous.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => hB (x - e))
  have hp : Integrable (fun x => g (x + e) * φ.val x) volume := by
    have h := (measurePreserving_add_right volume e).integrable_comp_of_integrable hm
    simpa only [Function.comp_def, add_sub_cancel_right] using h
  have he : (∫ x, g (x + e) * φ.val x) = ∫ x, g x * φ.val (x - e) := by
    have h := integral_add_right_eq_self (μ := volume) (fun x => g x * φ.val (x - e)) e
    simpa only [add_sub_cancel_right] using h
  calc
    (∫ x, diffQuot i t g x * φ.val x) =
        (∫ x, g (x + e) * φ.val x - g x * φ.val x) / t := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [diffQuot, e]
      ring
    _ = ((∫ x, g x * φ.val (x - e)) - ∫ x, g x * φ.val x) / t := by
      rw [integral_sub hp h0, he]
    _ = ∫ x, ((φ.val (x - t • EuclideanSpace.single i (1 : ℝ)) - φ.val x) / t) * g x := by
      rw [← integral_sub hm h0, ← integral_div]
      apply integral_congr_ae
      filter_upwards with x
      dsimp [e]
      ring

theorem integral_difference_test_tendsto {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))} (φ : testSpace Ω)
    (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : Integrable g volume) (i : Fin n) :
    Tendsto (fun t : ℝ => ∫ x, diffQuot i t g x * φ.val x)
      (𝓝[>] 0) (𝓝 (-∫ x, g x * Shared.partialDeriv φ.val i x)) := by
  simpa only [integral_difference_test_adjoint φ g hg] using
    test_backward_difference_limit φ g hg i

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE TestDifferenceAdjoint

-- BEGIN COMPLETE MODULE BoundedTestRepresentation
section

open scoped RealInnerProductSpace

namespace HunterPDE.Regularity.Proof

/-- A functional bounded by the Hilbert norm of a linear image is represented in that
Hilbert space. This lets bounded distributional tests produce an actual L² derivative. -/
theorem bounded_test_representation
    {V H : Type*} [AddCommGroup V] [Module ℝ V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (J : V →ₗ[ℝ] H) (L : V →ₗ[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ v, |L v| ≤ C * ‖J v‖) :
    ∃ g : H, ‖g‖ ≤ C ∧ ∀ v, inner ℝ g (J v) = L v := by
  classical
  have heq : ∀ v w, J v = J w → L v = L w := by
    intro v w h
    have hb := hbound (v - w)
    have hz : J (v - w) = 0 := by rw [map_sub, h, sub_self]
    rw [hz, norm_zero, mul_zero, map_sub] at hb
    exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)
  let pre : J.range → V := fun x => x.property.choose
  have hpre : ∀ x : J.range, J (pre x) = x := fun x => x.property.choose_spec
  let F : J.range →ₗ[ℝ] ℝ :=
    { toFun := fun x => L (pre x)
      map_add' := by
        intro x y
        rw [← map_add]
        apply heq
        rw [map_add, hpre, hpre, hpre]
        rfl
      map_smul' := by
        intro c x
        simp only [RingHom.id_apply]
        rw [← map_smul]
        apply heq
        rw [map_smul, hpre, hpre]
        rfl }
  have hF : ∀ x : J.range, ‖F x‖ ≤ C * ‖x‖ := by
    intro x
    change |L (pre x)| ≤ C * ‖(x : H)‖
    simpa only [hpre] using hbound (pre x)
  let Fc : J.range →L[ℝ] ℝ := F.mkContinuous C hF
  obtain ⟨G, hG, hnorm⟩ := exists_extension_norm_eq J.range Fc
  let g := (InnerProductSpace.toDual ℝ H).symm G
  refine ⟨g, ?_, ?_⟩
  · change ‖(InnerProductSpace.toDual ℝ H).symm G‖ ≤ C
    rw [LinearIsometryEquiv.norm_map, hnorm]
    exact Fc.opNorm_le_bound hC hF
  · intro v
    change inner ℝ ((InnerProductSpace.toDual ℝ H).symm G) (J v) = L v
    rw [InnerProductSpace.toDual_symm_apply]
    have hh := hG ⟨J v, ⟨v, rfl⟩⟩
    rw [hh]
    exact heq _ _ (hpre ⟨J v, ⟨v, rfl⟩⟩)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE BoundedTestRepresentation

-- BEGIN COMPLETE MODULE DistributionRepresentation
section

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace HunterPDE.Regularity.Proof

variable {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}

noncomputable def derivativeTestFunctional (u : EuclideanSpace ℝ (Fin n) → ℝ)
    (hu : MemLp u 2 (volume.restrict Ω)) (i : Fin n) : testSpace Ω →ₗ[ℝ] ℝ where
  toFun φ := -∫ x in Ω, u x * testPartial Ω i φ x
  map_add' φ ψ := by
    simp only [map_add, Pi.add_apply, mul_add]
    have hφ : Integrable (fun x => u x * testPartial Ω i φ x) (volume.restrict Ω) :=
      hu.integrable_mul (testPartial_memLp Ω i φ)
    have hψ : Integrable (fun x => u x * testPartial Ω i ψ x) (volume.restrict Ω) :=
      hu.integrable_mul (testPartial_memLp Ω i ψ)
    rw [integral_add hφ hψ]
    ring
  map_smul' c φ := by
    simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    simp_rw [mul_left_comm (u _) c]
    rw [integral_const_mul]
    ring

/-- A uniform bound on distributional differentiation against tests produces an L²
representative, with its quantitative norm bound. -/
theorem distributional_L2_representative
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemLp u 2 (volume.restrict Ω))
    (i : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ : testSpace Ω,
      |∫ x in Ω, u x * testPartial Ω i φ x| ≤ C * ‖testToLp Ω φ‖) :
    ∃ g : EuclideanSpace ℝ (Fin n) → ℝ, MemLp g 2 (volume.restrict Ω) ∧
      (eLpNorm g 2 (volume.restrict Ω)).toReal ≤ C ∧
      ∀ φ : testSpace Ω, ∫ x in Ω, g x * φ.val x =
        -∫ x in Ω, u x * testPartial Ω i φ x := by
  obtain ⟨g, hg, hrepr⟩ := bounded_test_representation (testToLp Ω)
    (derivativeTestFunctional u hu i) C hC (fun φ => by
      simpa only [derivativeTestFunctional, LinearMap.coe_mk, AddHom.coe_mk, abs_neg]
        using hbound φ)
  refine ⟨g, Lp.memLp g, ?_, ?_⟩
  · simpa only [← Lp.norm_def] using hg
  · intro φ
    have hh := hrepr φ
    rw [L2.inner_def] at hh
    change (∫ x in Ω, (testToLp Ω φ) x * g x) = _ at hh
    change _ = derivativeTestFunctional u hu i φ
    rw [← hh]
    apply integral_congr_ae
    filter_upwards [(test_memLp Ω φ).coeFn_toLp] with x hx
    change (testToLp Ω φ) x = φ.val x at hx
    rw [hx, mul_comm]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE DistributionRepresentation

-- BEGIN COMPLETE MODULE WeakDerivativeFromBound
section

open MeasureTheory Set
open scoped ENNReal

namespace HunterPDE.Regularity.Proof

/-- Quantitative distributional differentiation in L², expressed with the exact native
weak-derivative predicate and without choosing a weakly convergent subsequence. -/
theorem weak_derivative_of_test_bound {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : MemLp u 2 (volume.restrict Ω))
    (i : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ φ, Shared.IsTestFunction Ω φ →
      |∫ x in Ω, u x * Shared.partialDeriv φ i x| ≤
        C * (eLpNorm φ 2 (volume.restrict Ω)).toReal) :
    ∃ g, Shared.HasWeakDeriv Ω (Pi.single i 1) u g ∧
      MemLp g 2 (volume.restrict Ω) ∧
      (eLpNorm g 2 (volume.restrict Ω)).toReal ≤ C := by
  obtain ⟨g, hg, hnorm, hint⟩ := distributional_L2_representative u hu i C hC
    (fun φ => by simpa only [norm_testToLp, testPartial, LinearMap.coe_mk, AddHom.coe_mk] using hbound φ φ.property)
  refine ⟨g, ⟨?_, ?_, ?_⟩, hg, hnorm⟩
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hu.locallyIntegrable (by norm_num))
  · exact locallyIntegrableOn_of_locallyIntegrable_restrict (hg.locallyIntegrable (by norm_num))
  · intro φ hφ
    have hs : ∑ j, (Pi.single i 1 : Fin n → ℕ) j = 1 := by simp [Pi.single_apply]
    simpa only [multiDeriv_single, hs, pow_one, neg_one_mul, testPartial,
      LinearMap.coe_mk, AddHom.coe_mk] using hint ⟨φ, hφ⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE WeakDerivativeFromBound

-- BEGIN COMPLETE MODULE DifferenceQuotientConverse
section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace HunterPDE.Regularity.Proof

/-- Local L² bounds on difference quotients give a native weak derivative. The input
is globally integrable, as will hold after localizing the original solution. -/
theorem weak_derivative_of_difference_bound {n : ℕ}
    {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (u : EuclideanSpace ℝ (Fin n) → ℝ) (hu : Integrable u volume)
    (hu2 : MemLp u 2 (volume.restrict Ω)) (i : Fin n) (C : ℝ) (hC : 0 ≤ C)
    (hquot : ∀ᶠ t : ℝ in 𝓝[>] 0,
      MemLp (diffQuot i t u) 2 (volume.restrict Ω) ∧
      l2Norm (volume.restrict Ω) (diffQuot i t u) ≤ C) :
    ∃ g, Shared.HasWeakDeriv Ω (Pi.single i 1) u g ∧
      MemLp g 2 (volume.restrict Ω) ∧
      l2Norm (volume.restrict Ω) g ≤ C := by
  apply weak_derivative_of_test_bound u hu2 i C hC
  intro φ hφ
  let ψ : testSpace Ω := ⟨φ, hφ⟩
  have ht := (integral_difference_test_tendsto ψ u hu i).abs
  have hi : (∫ x in Ω, u x * Shared.partialDeriv φ i x) =
      ∫ x, u x * Shared.partialDeriv φ i x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    have hz : Shared.partialDeriv φ i x = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      exact fun hh => hx ((testPartial_isTest Ω i ψ).2.2 hh)
    rw [hz, mul_zero]
  rw [hi]
  have hlim : |-(∫ x, u x * Shared.partialDeriv φ i x)| ≤
      C * (eLpNorm φ 2 (volume.restrict Ω)).toReal := by
    apply le_of_tendsto ht
    filter_upwards [hquot] with t ht
    have he : (∫ x in Ω, diffQuot i t u x * φ x) =
        ∫ x, diffQuot i t u x * φ x := by
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro x hx
      rw [image_eq_zero_of_notMem_tsupport (fun hh => hx (hφ.2.2 hh)), mul_zero]
    rw [← he]
    exact (abs_integral_mul_le_l2 ht.1 (test_memLp Ω ψ)).trans
      (mul_le_mul_of_nonneg_right ht.2 (l2Norm_nonneg _ _))
  simpa only [abs_neg] using hlim

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE DifferenceQuotientConverse

-- BEGIN COMPLETE MODULE InteriorSecondDerivatives
section

open MeasureTheory Set Filter
open scoped Topology ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

 theorem InteriorSetup.second_derivative {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (hΩ' : MeasurableSet Ω') {a : Fin n → Fin n → E → ℝ} (S : InteriorSetup Ω Ω' a)
    (ha : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (hac : ∀ i j, ContinuousOn (a i j) Ω) {θ : ℝ} (hell : UniformlyElliptic Ω a θ)
    (f u : E → ℝ) (U : H1Data Ω u) (hsol : IsWeakSolution Ω a f u)
    (hf : MemLp f 2 (volume.restrict Ω)) (i j : Fin n) :
    ∃ v, Shared.HasWeakDeriv Ω' (Pi.single j 1) (U.grad i) v ∧
      MemLp v 2 (volume.restrict Ω') ∧ l2Norm (volume.restrict Ω') v ≤
        S.quotientConstant θ * (l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u) := by
  let J := U.cutoff hΩ S.χ_test
  let C := S.quotientConstant θ * (l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u)
  have hC : 0 ≤ C := mul_nonneg (S.quotientConstant_pos hell.1).le
    (add_nonneg (l2Norm_nonneg _ _) (l2Norm_nonneg _ _))
  have hp : MemLp (J.grad i) 2 volume := by simpa using J.grad_memLp i
  have hi := cutoff_gradient_integrable U hΩ S.χ_test i
  have hquot : ∀ᶠ t : ℝ in 𝓝[>] 0,
      MemLp (diffQuot j t (J.grad i)) 2 (volume.restrict Ω') ∧
      l2Norm (volume.restrict Ω') (diffQuot j t (J.grad i)) ≤ C := by
    have ht : ∀ᶠ t : ℝ in 𝓝[>] 0, t < S.ε :=
      eventually_nhdsWithin_of_eventually_nhds (eventually_lt_nhds S.ε_pos)
    filter_upwards [self_mem_nhdsWithin,ht] with t htpos htε
    have hpos : 0 < t := htpos
    refine ⟨(quotient_memLp hp j t).restrict Ω', ?_⟩
    exact S.quotient_bound hΩ hΩ' ha hac hell f u U hsol hf i j t
      (ne_of_gt hpos) (by rw [abs_of_pos hpos]; exact htε.le)
  obtain ⟨v,hw,hv,hN⟩ := weak_derivative_of_difference_bound (J.grad i) hi (hp.restrict Ω') j C hC hquot
  refine ⟨v,?_,hv,hN⟩
  apply weak_congr hw _ Filter.EventuallyEq.rfl
  filter_upwards [ae_restrict_mem hΩ'] with x hx
  exact cutoff_local_gradient U hΩ S.χ_test S.inner_open S.χ_one i (S.target_subset hx)

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE InteriorSecondDerivatives

-- BEGIN COMPLETE MODULE SecondWeakDerivative
section

open MeasureTheory Set

namespace HunterPDE.Regularity.Proof

lemma multiIndexList_length {n : ℕ} (α : Fin n → ℕ) :
    (Shared.multiIndexList α).length = ∑ i, α i := by
  simp [Shared.multiIndexList, List.length_flatMap, Fin.sum_univ_def]

theorem weak_second_compose {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u g h : EuclideanSpace ℝ (Fin n) → ℝ} {i j : Fin n} {α : Fin n → ℕ}
    (hg : Shared.HasWeakDeriv Ω (Pi.single i 1) u g)
    (hh : Shared.HasWeakDeriv Ω (Pi.single j 1) g h)
    (hα : Shared.multiIndexList α = [i, j]) : Shared.HasWeakDeriv Ω α u h := by
  refine ⟨hg.1, hh.2.1, ?_⟩
  intro φ hφ
  have h1 := hh.2.2 φ hφ
  have h2 := hg.2.2 (Shared.partialDeriv φ j) (test_partial hφ j)
  have hi : ∑ k, (Pi.single i 1 : Fin n → ℕ) k = 1 := by simp [Pi.single_apply]
  have hj : ∑ k, (Pi.single j 1 : Fin n → ℕ) k = 1 := by simp [Pi.single_apply]
  have hs : ∑ k, α k = 2 := by rw [← multiIndexList_length, hα]; rfl
  simp only [multiDeriv_single, hi, hj, pow_one, neg_one_mul] at h1 h2
  rw [h1, h2]
  simp only [hs, neg_neg, even_two, Even.neg_pow, one_pow, one_mul,
    Shared.multiDeriv, hα, Shared.iteratedPartial]

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SecondWeakDerivative

-- BEGIN COMPLETE MODULE H2Witness
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

structure H2Data {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n)))
    (u : EuclideanSpace ℝ (Fin n) → ℝ) extends H1Data Ω u where
  second : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ
  second_weak : ∀ i j, Shared.HasWeakDeriv Ω (Pi.single j 1) (grad i) (second i j)
  second_memLp : ∀ i j, MemLp (second i j) 2 (volume.restrict Ω)

theorem H2Data.memW {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (H : H2Data Ω u) : MemW 2 2 Ω u := by
  intro α hα
  have hlen : (Shared.multiIndexList α).length ≤ 2 := by
    rw [multiIndexList_length]
    exact (multi_mem_iff 2 α).mp hα
  cases he : Shared.multiIndexList α with
  | nil =>
    have hs : ∑ i, α i = 0 := by rw [← multiIndexList_length, he]; rfl
    refine ⟨u, ⟨memLp_locally H.self_memLp, memLp_locally H.self_memLp, ?_⟩, H.self_memLp⟩
    intro φ _
    simp only [hs, pow_zero, one_mul, Shared.multiDeriv, he, Shared.iteratedPartial]
  | cons i l =>
    cases l with
    | nil =>
      have hs : ∑ k, α k = 1 := by rw [← multiIndexList_length, he]; rfl
      refine ⟨H.grad i, ⟨(H.weak i).1, (H.weak i).2.1, ?_⟩, H.grad_memLp i⟩
      intro φ hφ
      have hh := (H.weak i).2.2 φ hφ
      have hi : ∑ k, (Pi.single i 1 : Fin n → ℕ) k = 1 := by simp [Pi.single_apply]
      simp only [hi, multiDeriv_single] at hh
      simpa only [hs, Shared.multiDeriv, he, Shared.iteratedPartial] using hh
    | cons j l =>
      have hl : l = [] := by simpa [he] using hlen
      subst l
      exact ⟨H.second i j, weak_second_compose (H.weak i) (H.second_weak i j) he,
        H.second_memLp i j⟩

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H2Witness

-- BEGIN COMPLETE MODULE SobolevNormBound
section

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity.Proof

theorem sobolevNorm_two_bound {n k : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ α ∈ multiIndicesLe n k,
      eLpNorm (Shared.weakDeriv Ω α u) 2 (volume.restrict Ω) ≤ ENNReal.ofReal B) :
    sobolevNorm k 2 Ω u ≤
      ENNReal.ofReal (((multiIndicesLe n k).card + 1 : ℝ) * B) := by
  let s := multiIndicesLe n k
  have hc : 0 ≤ (s.card : ℝ) := Nat.cast_nonneg _
  have hb : (∑ α ∈ s, eLpNorm (Shared.weakDeriv Ω α u) 2
      (volume.restrict Ω) ^ (2 : ℝ)) ≤
      ENNReal.ofReal (((s.card : ℝ) + 1) * B) ^ (2 : ℝ) := by
    calc
      _ ≤ ∑ _α ∈ s, (ENNReal.ofReal B) ^ (2 : ℝ) :=
        Finset.sum_le_sum (fun α hα => ENNReal.rpow_le_rpow (h α hα) (by norm_num))
      _ = ENNReal.ofReal ((s.card : ℝ) * B ^ 2) := by
        simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow, hB]
      _ ≤ ENNReal.ofReal ((((s.card : ℝ) + 1) * B) ^ 2) := by
        apply ENNReal.ofReal_le_ofReal
        nlinarith [sq_nonneg (s.card : ℝ), sq_nonneg B,
          mul_nonneg (sq_nonneg (s.card : ℝ)) (sq_nonneg B)]
      _ = _ := by rw [ENNReal.rpow_two, ENNReal.ofReal_pow (by positivity)]
  have hp := ENNReal.rpow_le_rpow hb (show (0 : ℝ) ≤ 1 / 2 by norm_num)
  rw [← ENNReal.rpow_mul] at hp
  norm_num only [show (2 : ℝ) * (1 / 2) = 1 by norm_num, ENNReal.rpow_one] at hp
  simpa [sobolevNorm, s] using hp

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE SobolevNormBound

-- BEGIN COMPLETE MODULE H2NormBound
section

open MeasureTheory

namespace HunterPDE.Regularity.Proof

theorem H2Data.bounded_witnesses {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    {u : EuclideanSpace ℝ (Fin n) → ℝ} (H : H2Data Ω u) {B : ℝ}
    (hu : l2Norm (volume.restrict Ω) u ≤ B)
    (hg : ∀ i, l2Norm (volume.restrict Ω) (H.grad i) ≤ B)
    (hh : ∀ i j, l2Norm (volume.restrict Ω) (H.second i j) ≤ B) :
    ∀ α ∈ multiIndicesLe n 2, ∃g, Shared.HasWeakDeriv Ω α u g ∧
      MemLp g 2 (volume.restrict Ω) ∧ l2Norm (volume.restrict Ω) g ≤ B := by
  intro α hα
  have hlen : (Shared.multiIndexList α).length ≤ 2 := by
    rw [multiIndexList_length]
    exact (multi_mem_iff 2 α).mp hα
  cases he : Shared.multiIndexList α with
  | nil =>
    have hs : ∑ i, α i = 0 := by rw [← multiIndexList_length, he]; rfl
    refine ⟨u, ⟨memLp_locally H.self_memLp, memLp_locally H.self_memLp, ?_⟩, H.self_memLp, hu⟩
    intro φ _
    simp only [hs, pow_zero, one_mul, Shared.multiDeriv, he, Shared.iteratedPartial]
  | cons i l =>
    cases l with
    | nil =>
      have hs : ∑ k, α k = 1 := by rw [← multiIndexList_length, he]; rfl
      refine ⟨H.grad i, ⟨(H.weak i).1, (H.weak i).2.1, ?_⟩, H.grad_memLp i, hg i⟩
      intro φ hφ
      have hh := (H.weak i).2.2 φ hφ
      have hi : ∑ k, (Pi.single i 1 : Fin n → ℕ) k = 1 := by simp [Pi.single_apply]
      simp only [hi, multiDeriv_single] at hh
      simpa only [hs, Shared.multiDeriv, he, Shared.iteratedPartial] using hh
    | cons j l =>
      have hl : l = [] := by simpa [he] using hlen
      subst l
      exact ⟨H.second i j, weak_second_compose (H.weak i) (H.second_weak i j) he,
        H.second_memLp i j, hh i j⟩


theorem H2Data.norm_bound {n : ℕ} {Ω : Set (EuclideanSpace ℝ (Fin n))}
    (hΩ : IsOpen Ω) {u : EuclideanSpace ℝ (Fin n) → ℝ} (H : H2Data Ω u)
    {B : ℝ} (hB : 0 ≤ B)
    (hu : l2Norm (volume.restrict Ω) u ≤ B)
    (hg : ∀ i, l2Norm (volume.restrict Ω) (H.grad i) ≤ B)
    (hh : ∀ i j, l2Norm (volume.restrict Ω) (H.second i j) ≤ B) :
    sobolevNorm 2 2 Ω u ≤ ENNReal.ofReal (((multiIndicesLe n 2).card + 1 : ℝ) * B) := by
  apply sobolevNorm_two_bound hB
  intro α hα
  obtain ⟨g, hw, hp, hb⟩ := H.bounded_witnesses hu hg hh α hα
  rw [eLpNorm_congr_ae (chosen_weakDeriv_ae hΩ hw)]
  rw [← ENNReal.ofReal_toReal hp.eLpNorm_ne_top]
  exact ENNReal.ofReal_le_ofReal hb

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE H2NormBound

-- BEGIN COMPLETE MODULE InteriorH2Estimate
section

open MeasureTheory Set
open scoped ENNReal
namespace HunterPDE.Regularity.Proof
variable {n : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin n)

 theorem InteriorSetup.h2_estimate {Ω Ω' : Set E} (hΩ : IsOpen Ω)
    (hΩ' : IsOpen Ω') {a : Fin n → Fin n → E → ℝ} (S : InteriorSetup Ω Ω' a)
    (ha : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (hac : ∀ i j, ContinuousOn (a i j) Ω) {θ : ℝ} (hell : UniformlyElliptic Ω a θ) :
    ∃ C : ℝ, ∀ f u : E → ℝ, MemLp f 2 (volume.restrict Ω) → IsWeakSolution Ω a f u →
      MemW 2 2 Ω' u ∧ sobolevNorm 2 2 Ω' u ≤ ENNReal.ofReal C *
        (eLpNorm f 2 (volume.restrict Ω) + eLpNorm u 2 (volume.restrict Ω)) := by
  let B : ℝ := 1 + S.C + S.quotientConstant θ
  have hq := S.quotientConstant_pos hell.1
  have hB : 0 ≤ B := by dsimp [B]; linarith [S.C_pos]
  let C : ℝ := ((multiIndicesLe n 2).card + 1 : ℝ) * B
  have hC : 0 ≤ C := mul_nonneg (by positivity) hB
  refine ⟨C,?_⟩
  intro f u hf hsol
  obtain ⟨U⟩ := h1Data_exists hΩ hsol.1
  let T := l2Norm (volume.restrict Ω) f + l2Norm (volume.restrict Ω) u
  have hF := l2Norm_nonneg (volume.restrict Ω) f
  have hU := l2Norm_nonneg (volume.restrict Ω) u
  have hT : 0 ≤ T := add_nonneg hF hU
  have hsub : Ω' ⊆ Ω := S.target_subset.trans S.inner_subset
  choose v hv hp hN using S.second_derivative hΩ hΩ'.measurableSet ha hac hell f u U hsol hf
  let H : H2Data Ω' u := {
    toH1Data := U.restrict hsub
    second := v
    second_weak := hv
    second_memLp := hp }
  refine ⟨H.memW,?_⟩
  have huN : l2Norm (volume.restrict Ω') u ≤ B * T := by
    have huL := l2Norm_mono_measure U.self_memLp (Measure.restrict_mono hsub le_rfl)
    have hBT : T ≤ B * T := by
      have h1 : 1 ≤ B := by dsimp [B]; linarith [S.C_pos]
      nlinarith
    exact huL.trans ((by dsimp [T]; linarith : l2Norm (volume.restrict Ω) u ≤ T).trans hBT)
  have hgN (i : Fin n) : l2Norm (volume.restrict Ω') (H.grad i) ≤ B * T := by
    let J := U.cutoff hΩ S.χ_test
    have he : l2Norm (volume.restrict Ω') (H.grad i) = l2Norm (volume.restrict Ω') (J.grad i) := by
      apply l2Norm_restrict_eqOn hΩ'.measurableSet
      intro x hx
      exact (cutoff_local_gradient U hΩ S.χ_test S.inner_open S.χ_one i (S.target_subset hx)).symm
    rw [he]
    have hpJ : MemLp (J.grad i) 2 volume := by simpa using J.grad_memLp i
    have hmono := l2Norm_mono_measure hpJ (Measure.restrict_le_self (s := Ω'))
    have hlocal := S.gradient_bound f u U hΩ hsol hf i
    have hCB : S.C * T ≤ B * T := by
      apply mul_le_mul_of_nonneg_right _ hT
      dsimp [B]; linarith
    exact hmono.trans (hlocal.trans hCB)
  have hhN (i j : Fin n) : l2Norm (volume.restrict Ω') (H.second i j) ≤ B * T := by
    apply (hN i j).trans
    apply mul_le_mul_of_nonneg_right _ hT
    dsimp [B]; linarith [S.C_pos]
  have hnorm := H.norm_bound hΩ' (mul_nonneg hB hT) huN hgN hhN
  have he : ENNReal.ofReal (((multiIndicesLe n 2).card + 1 : ℝ) * (B * T)) =
      ENNReal.ofReal C * (eLpNorm f 2 (volume.restrict Ω) + eLpNorm u 2 (volume.restrict Ω)) := by
    rw [← mul_assoc]
    change ENNReal.ofReal (C * T) = _
    rw [ENNReal.ofReal_mul hC]
    dsimp [T,l2Norm]
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hf.2.ne,
      ENNReal.ofReal_toReal U.self_memLp.2.ne]
  exact hnorm.trans_eq he

end HunterPDE.Regularity.Proof
end
-- END COMPLETE MODULE InteriorH2Estimate

-- BEGIN COMPLETE MODULE HunterH2Root
section

open MeasureTheory
open scoped ENNReal

namespace HunterPDE.Regularity

/-- Theorem 4.27 of Hunter, *Notes on PDEs* (revised 6/18/2014), p. 112 (interior `H²`
regularity): let `Ω` be an open set in `ℝⁿ`, `aᵢⱼ ∈ C¹(Ω)` and `f ∈ L²(Ω)`. If `u ∈ H¹(Ω)` is a
weak solution of `L u = −∑ᵢⱼ ∂ᵢ(aᵢⱼ ∂ⱼu) = f` ((4.34)–(4.37)), then `u ∈ H²(Ω′)` for every
`Ω′ ⋐ Ω`, and (4.39) `‖u‖_{H²(Ω′)} ≤ C (‖f‖_{L²(Ω)} + ‖u‖_{L²(Ω)})` where `C` depends only on
`n`, `Ω′`, `Ω` and `aᵢⱼ`.
The standing assumptions of §4.6 on `L` are hypotheses: `aᵢⱼ ∈ L^∞(Ω)`, `aᵢⱼ = aⱼᵢ` ((4.17)) and
uniform ellipticity with constant `θ` ((4.18)). `C¹(Ω)` is `ContDiffOn ℝ 1` on `Ω` (no
regularity up to the boundary, as printed). The constant `C` is chosen after `Ω`, the
coefficients (and their ellipticity constant) and `Ω′`, and before `f` and `u`. -/
theorem interior_H2_regularity {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_C1 : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (ha_bdd : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (ha_symm : ∀ i j, a i j = a j i) (θ : ℝ) (hθ : UniformlyElliptic Ω a θ)
    (Ω' : Set (EuclideanSpace ℝ (Fin n))) (hΩ' : CompactlyContained Ω' Ω) :
    ∃ C : ℝ, ∀ f u : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp f 2 (volume.restrict Ω) → IsWeakSolution Ω a f u →
        MemW 2 2 Ω' u ∧
          sobolevNorm 2 2 Ω' u ≤ ENNReal.ofReal C *
            (eLpNorm f 2 (volume.restrict Ω) + eLpNorm u 2 (volume.restrict Ω)) := by
  have _symmetry := ha_symm
  obtain ⟨S⟩ := Proof.interior_setup_exists hΩ hΩ' a ha_C1 ha_bdd θ hθ
  exact S.h2_estimate hΩ hΩ'.2.1 ha_bdd (fun i j => (ha_C1 i j).continuousOn) hθ

end HunterPDE.Regularity

open HunterPDE.Regularity

theorem solution {n : ℕ} (Ω : Set (EuclideanSpace ℝ (Fin n))) (hΩ : IsOpen Ω)
    (a : Fin n → Fin n → EuclideanSpace ℝ (Fin n) → ℝ)
    (ha_C1 : ∀ i j, ContDiffOn ℝ 1 (a i j) Ω)
    (ha_bdd : ∀ i j, MemLp (a i j) ∞ (volume.restrict Ω))
    (ha_symm : ∀ i j, a i j = a j i) (θ : ℝ) (hθ : UniformlyElliptic Ω a θ)
    (Ω' : Set (EuclideanSpace ℝ (Fin n))) (hΩ' : CompactlyContained Ω' Ω) :
    ∃ C : ℝ, ∀ f u : EuclideanSpace ℝ (Fin n) → ℝ,
      MemLp f 2 (volume.restrict Ω) → IsWeakSolution Ω a f u →
        MemW 2 2 Ω' u ∧
          sobolevNorm 2 2 Ω' u ≤ ENNReal.ofReal C *
            (eLpNorm f 2 (volume.restrict Ω) + eLpNorm u 2 (volume.restrict Ω)) := by
  exact interior_H2_regularity Ω hΩ a ha_C1 ha_bdd ha_symm θ hθ Ω' hΩ'
end
-- END COMPLETE MODULE HunterH2Root
