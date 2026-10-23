-- Prove2me | solution 1 for JHolomorphic.tendstoCInftyLocOn_tangent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T07:36:45.855773+00:00
-- url     : https://prove2.me/submissions/6b990d94-a3bb-46db-ad35-6aa4ecab6f6f

import Mathlib
import Definitions.Def_JHolomorphic_Setting

set_option linter.all false
set_option maxSynthPendingDepth 3

namespace TanDev

open MeasureTheory Metric Filter Topology Set ContinuousLinearMap
open scoped ContDiff ENNReal NNReal

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- the tangent structure -/
def T (F : E → E →L[ℝ] E) : E × E → (E × E →L[ℝ] E × E) := fun x =>
  ((F x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
    ((F x.1).comp (ContinuousLinearMap.snd ℝ E E) +
      (fderiv ℝ F x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E))

def compR (g : E × E →L[ℝ] E) : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E) :=
  (ContinuousLinearMap.compL ℝ (E × E) E E).flip g

def Φ₁ : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E) :=
  (ContinuousLinearMap.prodₗᵢ ℝ).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((compR (ContinuousLinearMap.fst ℝ E E)).prod (compR (ContinuousLinearMap.snd ℝ E E)))

def P : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E) :=
  (ContinuousLinearMap.compL ℝ (E × E) E (E × E) (ContinuousLinearMap.inr ℝ E E)).comp
    (compR (ContinuousLinearMap.fst ℝ E E))

def B : (E →L[ℝ] (E →L[ℝ] E)) →L[ℝ] E →L[ℝ] (E × E →L[ℝ] E × E) :=
  ContinuousLinearMap.compL ℝ E (E →L[ℝ] E) (E × E →L[ℝ] E × E) P

lemma Φ₁_apply (A : E →L[ℝ] E) :
    Φ₁ A = (A.comp (ContinuousLinearMap.fst ℝ E E)).prod (A.comp (ContinuousLinearMap.snd ℝ E E)) :=
  rfl

lemma T_eq (F : E → E →L[ℝ] E) (x : E × E) :
    T F x = Φ₁ (F x.1) + B (fderiv ℝ F x.1) x.2 := by
  ext v <;> simp [T, Φ₁_apply, B, P, compR]

section bound
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

lemma comp_fst_le {O : Set E} (hO : IsOpen O) {f : E → X} (hf : ContDiffOn ℝ ∞ f O) (i : ℕ)
    {p : E × E} (hp : p.1 ∈ O) :
    ‖iteratedFDerivWithin ℝ i (fun q : E × E => f q.1) (Prod.fst ⁻¹' O) p‖ ≤
      ‖iteratedFDerivWithin ℝ i f O p.1‖ := by
  have hW : IsOpen (Prod.fst ⁻¹' O : Set (E × E)) := hO.preimage continuous_fst
  have h := ContinuousLinearMap.iteratedFDerivWithin_comp_right (ContinuousLinearMap.fst ℝ E E)
    hf hO.uniqueDiffOn hW.uniqueDiffOn hp (i := i) (by exact_mod_cast le_top)
  change ‖iteratedFDerivWithin ℝ i (f ∘ (ContinuousLinearMap.fst ℝ E E))
    ((ContinuousLinearMap.fst ℝ E E) ⁻¹' O) p‖ ≤ _
  rw [h]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  exact Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ E E)

end bound

lemma T_bound {O : Set E} (hO : IsOpen O) {G : E → E →L[ℝ] E} (hG : ContDiffOn ℝ ∞ G O) (m : ℕ)
    {p : E × E} (hp : p.1 ∈ O) :
    ‖iteratedFDerivWithin ℝ m (T G) (Prod.fst ⁻¹' O) p‖ ≤
      ‖(Φ₁ : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E))‖ * ‖iteratedFDerivWithin ℝ m G O p.1‖ +
      ‖(B : (E →L[ℝ] (E →L[ℝ] E)) →L[ℝ] E →L[ℝ] (E × E →L[ℝ] E × E))‖ *
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ (i + 1) G O p.1‖ *
          ‖iteratedFDerivWithin ℝ (m - i) (fun q : E × E => q.2) (Prod.fst ⁻¹' O) p‖ := by
  set W : Set (E × E) := Prod.fst ⁻¹' O with hWdef
  have hW : IsOpen W := hO.preimage continuous_fst
  have hWu : UniqueDiffOn ℝ W := hW.uniqueDiffOn
  have hpW : p ∈ W := hp
  have hG1 : ContDiffOn ℝ ∞ (fun q : E × E => G q.1) W :=
    hG.comp contDiff_fst.contDiffOn (fun q hq => hq)
  have hdG : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x) O := hG.fderiv_of_isOpen hO (by simp)
  have hf1 : ContDiffOn ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) W :=
    hdG.comp contDiff_fst.contDiffOn (fun q hq => hq)
  have hsnd : ContDiffOn ℝ ∞ (fun q : E × E => q.2) W := contDiff_snd.contDiffOn
  have hA : ContDiffOn ℝ ∞ (fun q : E × E => Φ₁ (G q.1)) W :=
    (Φ₁ (E := E)).contDiff.comp_contDiffOn hG1
  have hBB : ContDiffOn ℝ ∞ (fun q : E × E => B (fderiv ℝ G q.1) q.2) W :=
    ((B (E := E)).contDiff.comp_contDiffOn hf1).clm_apply hsnd
  have hT : T G = (fun q : E × E => Φ₁ (G q.1)) + (fun q : E × E => B (fderiv ℝ G q.1) q.2) := by
    funext q; exact T_eq G q
  rw [hT, iteratedFDerivWithin_add_apply ((hA.contDiffWithinAt hpW).of_le (by exact_mod_cast le_top))
    ((hBB.contDiffWithinAt hpW).of_le (by exact_mod_cast le_top)) hWu hpW]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · have := Φ₁.norm_iteratedFDerivWithin_comp_left (hG1.contDiffWithinAt hpW) hWu hpW
      (n := m) (by exact_mod_cast le_top)
    refine this.trans (mul_le_mul_of_nonneg_left (comp_fst_le hO hG m hp) (norm_nonneg _))
  · have := B.norm_iteratedFDerivWithin_le_of_bilinear hf1 hsnd hWu hpW (n := m)
      (by exact_mod_cast le_top)
    refine this.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i hi => ?_) (norm_nonneg _))
    gcongr
    refine (comp_fst_le hO hdG i hp).trans (le_of_eq ?_)
    rw [← norm_iteratedFDerivWithin_fderivWithin hO.uniqueDiffOn hp]
    congr 1
    exact iteratedFDerivWithin_congr (𝕜 := ℝ) (n := i) (f₁ := fun x => fderiv ℝ G x) (f := fderivWithin ℝ G O)
      (fun x hx => (fderivWithin_of_isOpen hO hx).symm) hp

lemma T_contDiffOn {O : Set E} (hO : IsOpen O) {G : E → E →L[ℝ] E} (hG : ContDiffOn ℝ ∞ G O) :
    ContDiffOn ℝ ∞ (T G) (Prod.fst ⁻¹' O) := by
  have hG1 : ContDiffOn ℝ ∞ (fun q : E × E => G q.1) (Prod.fst ⁻¹' O) :=
    hG.comp contDiff_fst.contDiffOn (fun q hq => hq)
  have hdG : ContDiffOn ℝ ∞ (fun x => fderiv ℝ G x) O := hG.fderiv_of_isOpen hO (by simp)
  have hf1 : ContDiffOn ℝ ∞ (fun q : E × E => fderiv ℝ G q.1) (Prod.fst ⁻¹' O) :=
    hdG.comp contDiff_fst.contDiffOn (fun q hq => hq)
  have hT : T G = (fun q : E × E => Φ₁ (G q.1)) + (fun q : E × E => B (fderiv ℝ G q.1) q.2) := by
    funext q; exact T_eq G q
  rw [hT]
  exact ((Φ₁ (E := E)).contDiff.comp_contDiffOn hG1).add
    (((B (E := E)).contDiff.comp_contDiffOn hf1).clm_apply contDiff_snd.contDiffOn)

lemma T_sub {O : Set E} (hO : IsOpen O) {F G : E → E →L[ℝ] E} (hF : ContDiffOn ℝ ∞ F O)
    (hG : ContDiffOn ℝ ∞ G O) {q : E × E} (hq : q.1 ∈ O) :
    T F q - T G q = T (F - G) q := by
  have hFd : DifferentiableAt ℝ F q.1 :=
    (hF.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hq)
  have hGd : DifferentiableAt ℝ G q.1 :=
    (hG.differentiableOn (by simp)).differentiableAt (hO.mem_nhds hq)
  rw [T_eq, T_eq, T_eq, fderiv_sub hFd hGd]
  simp only [Pi.sub_apply, map_sub, ContinuousLinearMap.sub_apply]
  abel

theorem main (J : E → E →L[ℝ] E)
    (Jν : ℕ → E → E →L[ℝ] E) (O : Set E) (hJ : JHolomorphic.IsAlmostComplexOn J O)
    (hJν : ∀ ν, JHolomorphic.IsAlmostComplexOn (Jν ν) O)
    (hconv : JHolomorphic.TendstoCInftyLocOn Jν J O) :
    JHolomorphic.TendstoCInftyLocOn (fun ν => T (Jν ν)) (T J) (O ×ˢ Set.univ) := by
  intro K hK hKc m
  have hO : IsOpen O := hJ.1
  set W : Set (E × E) := Prod.fst ⁻¹' O with hWdef
  have hW : IsOpen W := hO.preimage continuous_fst
  have hWu : UniqueDiffOn ℝ W := hW.uniqueDiffOn
  rw [Set.prod_univ] at hK
  have hK1c : IsCompact (Prod.fst '' K) := hKc.image continuous_fst
  have hK1 : Prod.fst '' K ⊆ O := by rintro _ ⟨p, hp, rfl⟩; exact hK hp
  have hJs : ContDiffOn ℝ ∞ J O := hJ.2.1
  have hJνs : ∀ ν, ContDiffOn ℝ ∞ (Jν ν) O := fun ν => (hJν ν).2.1
  -- bound on derivatives of snd
  obtain ⟨M, hM0, hM⟩ : ∃ M, 0 ≤ M ∧ ∀ p ∈ K, ∑ j ∈ Finset.range (m + 1),
      ‖iteratedFDeriv ℝ j (fun q : E × E => q.2) p‖ ≤ M := by
    have hc : Continuous fun p : E × E => ∑ j ∈ Finset.range (m + 1),
        ‖iteratedFDeriv ℝ j (fun q : E × E => q.2) p‖ :=
      continuous_finset_sum _ fun j _ => (contDiff_snd.continuous_iteratedFDeriv
        (by exact_mod_cast le_top)).norm
    obtain ⟨M, hM⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
    exact ⟨max M 0, le_max_right _ _, fun p hp => le_max_of_le_left
      ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hM p hp))⟩
  have hMj : ∀ j ≤ m, ∀ p ∈ K, ‖iteratedFDerivWithin ℝ j (fun q : E × E => q.2) W p‖ ≤ M := by
    intro j hj p hp
    rw [iteratedFDerivWithin_of_isOpen j hW (hK hp)]
    refine le_trans ?_ (hM p hp)
    exact Finset.single_le_sum (f := fun j => ‖iteratedFDeriv ℝ j (fun q : E × E => q.2) p‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  set Cst : ℝ := ‖(Φ₁ : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E))‖ +
      ‖(B : (E →L[ℝ] (E →L[ℝ] E)) →L[ℝ] E →L[ℝ] (E × E →L[ℝ] E × E))‖ *
        ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * M with hCst
  have hCst0 : 0 ≤ Cst := by positivity
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  set δ := ε / (Cst + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hev : ∀ᶠ ν in atTop, ∀ k ∈ Finset.range (m + 2), ∀ x ∈ Prod.fst '' K,
      dist (iteratedFDeriv ℝ k J x) (iteratedFDeriv ℝ k (Jν ν) x) < δ :=
    (Filter.eventually_all_finset _).2 fun k _ =>
      Metric.tendstoUniformlyOn_iff.1 (hconv _ hK1 hK1c k) δ hδ0
  filter_upwards [hev] with ν hν p hp
  have hp1 : p.1 ∈ O := hK hp
  have hGs : ContDiffOn ℝ ∞ (Jν ν - J) O := (hJνs ν).sub hJs
  have hGk : ∀ k < m + 2, ‖iteratedFDerivWithin ℝ k (Jν ν - J) O p.1‖ ≤ δ := by
    intro k hk
    rw [iteratedFDerivWithin_sub_apply (((hJνs ν).contDiffWithinAt hp1).of_le
      (by exact_mod_cast le_top)) ((hJs.contDiffWithinAt hp1).of_le (by exact_mod_cast le_top))
      hO.uniqueDiffOn hp1, iteratedFDerivWithin_of_isOpen k hO hp1,
      iteratedFDerivWithin_of_isOpen k hO hp1, ← dist_eq_norm, dist_comm]
    exact (hν k (Finset.mem_range.2 hk) p.1 ⟨p, hp, rfl⟩).le
  have heq : iteratedFDeriv ℝ m (T (Jν ν)) p - iteratedFDeriv ℝ m (T J) p =
      iteratedFDerivWithin ℝ m (T (Jν ν - J)) W p := by
    rw [← iteratedFDerivWithin_of_isOpen m hW (hK hp), ← iteratedFDerivWithin_of_isOpen m hW (hK hp),
      ← iteratedFDerivWithin_sub_apply
        (((T_contDiffOn hO (hJνs ν)).contDiffWithinAt (hK hp)).of_le (by exact_mod_cast le_top))
        (((T_contDiffOn hO hJs).contDiffWithinAt (hK hp)).of_le (by exact_mod_cast le_top)) hWu (hK hp)]
    exact iteratedFDerivWithin_congr (𝕜 := ℝ) (n := m)
      (fun q hq => T_sub hO (hJνs ν) hJs hq) (hK hp)
  rw [dist_comm, dist_eq_norm, heq]
  refine lt_of_le_of_lt (T_bound hO hGs m hp1) ?_
  have h1 : ‖(Φ₁ : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E))‖ *
      ‖iteratedFDerivWithin ℝ m (Jν ν - J) O p.1‖ ≤
      ‖(Φ₁ : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E))‖ * δ :=
    mul_le_mul_of_nonneg_left (hGk m (by omega)) (norm_nonneg _)
  have h2 : ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) *
      ‖iteratedFDerivWithin ℝ (i + 1) (Jν ν - J) O p.1‖ *
        ‖iteratedFDerivWithin ℝ (m - i) (fun q : E × E => q.2) (Prod.fst ⁻¹' O) p‖ ≤
      δ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * M := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    calc (m.choose i : ℝ) * ‖iteratedFDerivWithin ℝ (i + 1) (Jν ν - J) O p.1‖ *
          ‖iteratedFDerivWithin ℝ (m - i) (fun q : E × E => q.2) (Prod.fst ⁻¹' O) p‖
        ≤ (m.choose i : ℝ) * δ * M := by
          gcongr
          · exact hGk (i + 1) (by omega)
          · exact hMj (m - i) (by omega) p hp
      _ = δ * ((m.choose i : ℝ) * M) := by ring
  have h3 : δ * Cst < ε := by
    rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by linarith)]
    nlinarith
  calc _ ≤ ‖(Φ₁ : (E →L[ℝ] E) →L[ℝ] (E × E →L[ℝ] E × E))‖ * δ +
        ‖(B : (E →L[ℝ] (E →L[ℝ] E)) →L[ℝ] E →L[ℝ] (E × E →L[ℝ] E × E))‖ *
          (δ * ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * M) := by
        gcongr
    _ = δ * Cst := by rw [hCst]; ring
    _ < ε := h3

end

end TanDev

open MeasureTheory Metric Filter Topology JHolomorphic
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (J : E → E →L[ℝ] E)
    (Jν : ℕ → E → E →L[ℝ] E) (O : Set E) (hJ : IsAlmostComplexOn J O)
    (hJν : ∀ ν, IsAlmostComplexOn (Jν ν) O) (hconv : TendstoCInftyLocOn Jν J O) :
    TendstoCInftyLocOn
      (fun ν (x : E × E) => ((Jν ν x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((Jν ν x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ (Jν ν) x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (fun x : E × E => ((J x.1).comp (ContinuousLinearMap.fst ℝ E E)).prod
        ((J x.1).comp (ContinuousLinearMap.snd ℝ E E) +
          (fderiv ℝ J x.1 x.2).comp (ContinuousLinearMap.fst ℝ E E)))
      (O ×ˢ Set.univ) :=
  TanDev.main J Jν O hJ hJν hconv
