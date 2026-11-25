-- Prove2me | solution 1 for GlobalTheory.PeriodSymm.symm_of_cocycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:42.941117+00:00
-- url     : https://prove2.me/submissions/738aec98-4929-43c0-bd34-ccafdf2c7325

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_SetIntegralFderivEqZeroOfLatticePeriodic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_CauchyRiemannIffDifferentiableOnComplex
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_PeriodicCechCocycleSmoothCoboundaryStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ThetaCocyclePeriodicNonvanishingSections
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_congr
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_holo
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_add
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_sub
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_mul
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_sum
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_anti
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_translate
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_contDiffAt
import Theorems.Thm_GlobalTheory_PeriodSymm_dbar_symm
import Theorems.Thm_GlobalTheory_T_exists_periodic_smooth_coboundary_of_cech_cocycle
import Theorems.Thm_GlobalTheory_cauchyRiemann_iff_differentiableOn_complex
import Theorems.Thm_GlobalTheory_const_eq_zero_of_sum_fderiv_periodic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
namespace GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
private lemma hasFDerivAt_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ}
    {A' : ι → E →L[ℝ] ℂ} {x : E} (h : ∀ i ∈ s, HasFDerivAt (A i) (A' i) x) :
    HasFDerivAt (fun y => ∑ i ∈ s, A i y) (∑ i ∈ s, A' i) x := by
  exact HasFDerivAt.fun_sum h
private lemma dbar_const_mul {f : E → ℂ} {z : E} (c : ℂ) (h : DifferentiableAt ℝ f z)
    (u : E) : dbar (fun x => c * f x) u z = c * dbar f u z := by
  have H : HasFDerivAt (fun x => c * f x) (c • fderiv ℝ f z) z := h.hasFDerivAt.const_mul c
  rw [dbar, dbar, H.fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring
private lemma contDiffAt_two_of_contDiffOn_infty_of_isOpen {s : Set E} {f : E → ℂ} {x : E} (hf : ContDiffOn ℝ ∞ f s)
    (hs : IsOpen s) (hx : x ∈ s) : ContDiffAt ℝ 2 f x := by
  have := (contDiffOn_infty.1 hf 2).contDiffAt (hs.mem_nhds hx)
  exact_mod_cast this
private lemma contDiffOn_infty_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ} {t : Set E}
    (h : ∀ i ∈ s, ContDiffOn ℝ ∞ (A i) t) : ContDiffOn ℝ ∞ (fun y => ∑ i ∈ s, A i y) t := by
  exact ContDiffOn.sum h
private lemma contDiffAt_one_finset_sum {ι : Type*} (s : Finset ι) {A : ι → E → ℂ} {x : E}
    (h : ∀ i ∈ s, ContDiffAt ℝ 1 (A i) x) : ContDiffAt ℝ 1 (fun y => ∑ i ∈ s, A i y) x := by
  exact ContDiffAt.sum h
end GlobalTheory.PeriodSymm
end

set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open Filter Topology
open GlobalTheory GlobalTheory.PeriodSymm
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace GlobalTheory.PeriodSymm
theorem _root_.solution (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (hd : DiscreteTopology Λ)
    (hsp : Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤) (ι : Type) (U : ι → Set (Fin g → ℂ))
    (p : ι → Fin g → (Fin g → ℂ) → ℂ) (k : ι → ι → (Fin g → ℂ) → ℂ)
    (θ h : Fin g → (Fin g → ℂ) →L[ℝ] ℂ)
    (hθ : ∀ m u, θ m (I • u) = -I * θ m u) (hh : ∀ m u, h m (I • u) = -I * h m u)
    (hU : ∀ i, IsOpen (U i)) (hinv : ∀ i (l : Λ) z, z ∈ U i → z + l ∈ U i)
    (hcov : ∀ z, ∃ i, z ∈ U i) (hp : ∀ i m, DifferentiableOn ℂ (p i m) (U i))
    (hper : ∀ i m (l : Λ), ∀ z ∈ U i, p i m (z + l) = p i m z - h m l)
    (hk : ∀ i j, DifferentiableOn ℂ (k i j) (U i ∩ U j))
    (hkc : ∀ i j m, ∀ z ∈ U i ∩ U j ∩ U m, k i j z + k j m z = k i m z)
    (hkp : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j,
      k i j (z + l) = k i j z + (∑ m, θ m l * p i m z - ∑ m, θ m l * p j m z))
    (u v : Fin g → ℂ) : ∑ m, θ m u * h m v = ∑ m, θ m v * h m u := by
  classical
  have hpS : ∀ i m, ContDiffOn ℝ ∞ (p i m) (U i) := fun i m =>
    ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g (U i) (p i m) (hU i)).2 (hp i m)).1
  have hkS : ∀ i j, ContDiffOn ℝ ∞ (k i j) (U i ∩ U j) := fun i j =>
    ((GlobalTheory.cauchyRiemann_iff_differentiableOn_complex g _ (k i j) ((hU i).inter (hU j))).2
      (hk i j)).1

  obtain ⟨G, hG⟩ : ∃ G : ι → ι → (Fin g → ℂ) → ℂ, ∀ i j z,
      G i j z = k i j z - ∑ m, θ m z * (p i m z - p j m z) := ⟨_, fun _ _ _ => rfl⟩
  have hGs : ∀ i j, ContDiffOn ℝ ∞ (G i j) (U i ∩ U j) := by
    intro i j
    refine ContDiffOn.congr ?_ (fun z _ => hG i j z)
    have hs : ContDiffOn ℝ ∞ (fun z => ∑ m, θ m z * (p i m z - p j m z)) (U i ∩ U j) :=
      contDiffOn_infty_finset_sum (A := fun m z => θ m z * (p i m z - p j m z)) Finset.univ fun m _ => by
        exact (θ m).contDiff.contDiffOn.mul
          (((hpS i m).mono Set.inter_subset_left).sub ((hpS j m).mono Set.inter_subset_right))
    exact (hkS i j).sub hs
  have hGper : ∀ i j (l : Λ), ∀ z ∈ U i ∩ U j, G i j (z + l) = G i j z := by
    intro i j l z hz
    have hi : ∀ m, p i m (z + l) = p i m z - h m l := fun m => hper i m l z hz.1
    have hj : ∀ m, p j m (z + l) = p j m z - h m l := fun m => hper j m l z hz.2
    rw [hG, hG, hkp i j l z hz]
    simp only [hi, hj, map_add, sub_sub_sub_cancel_right, add_mul, Finset.sum_add_distrib, mul_sub,
      Finset.sum_sub_distrib]
    ring
  have hGc : ∀ i j n, ∀ z ∈ U i ∩ U j ∩ U n, G i j z + G j n z = G i n z := by
    intro i j n z hz
    rw [hG, hG, hG, ← hkc i j n z hz]
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  obtain ⟨b, hb, hbG⟩ := GlobalTheory.T.exists_periodic_smooth_coboundary_of_cech_cocycle g Λ hd hsp ι U G hU hinv hcov hGs hGper hGc
  have hbA : ∀ i, ∀ x ∈ U i, ContDiffAt ℝ 2 (b i) x := fun i x hx =>
    contDiffAt_two_of_contDiffOn_infty_of_isOpen (hb i).1 (hU i) hx
  have hbD : ∀ i, ∀ x ∈ U i, DifferentiableAt ℝ (b i) x := fun i x hx =>
    (hbA i x hx).differentiableAt (by norm_num)
  have hpD : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℂ (p i m) x := fun i m x hx =>
    (hp i m).differentiableAt ((hU i).mem_nhds hx)

  obtain ⟨W, hW⟩ : ∃ W : ι → (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ i u,
      W i u = fun y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y :=
    ⟨fun i u y => (∑ m, (2 * θ m u) * (p i m y + h m y)) - dbar (b i) u y, fun _ _ => rfl⟩
  have hPH : ∀ i m, ∀ x ∈ U i, DifferentiableAt ℝ (fun y => p i m y + h m y) x := fun i m x hx =>
    ((hpD i m x hx).restrictScalars ℝ).add (h m).differentiableAt
  have hTD : ∀ i u m, ∀ x ∈ U i,
      DifferentiableAt ℝ (fun y => 2 * θ m u * (p i m y + h m y)) x := fun i u m x hx =>
    (hPH i m x hx).const_mul _
  have hSD : ∀ i u, ∀ x ∈ U i,
      DifferentiableAt ℝ (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x := fun i u x hx =>
    (hasFDerivAt_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ
      fun m _ => (hTD i u m x hx).hasFDerivAt).differentiableAt
  have hWA : ∀ i u, ∀ x ∈ U i, ContDiffAt ℝ 1 (W i u) x := by
    intro i u x hx
    have h1 : ContDiffAt ℝ 1 (fun y => ∑ m, (2 * θ m u) * (p i m y + h m y)) x :=
      contDiffAt_one_finset_sum (A := fun m y => 2 * θ m u * (p i m y + h m y)) Finset.univ fun m _ => by
        exact contDiffAt_const.mul
          (((contDiffAt_two_of_contDiffOn_infty_of_isOpen (hpS i m) (hU i) hx).of_le (by norm_num)).add
            (h m).contDiff.contDiffAt)
    have h2 := dbar_contDiffAt (hbA i x hx) u
    rw [hW]
    exact h1.sub h2
  have hWeq : ∀ i j u, ∀ x ∈ U i ∩ U j, W i u x = W j u x := by
    intro i j u x hx
    have hO : U i ∩ U j ∈ 𝓝 x := ((hU i).inter (hU j)).mem_nhds hx
    have hev : b j =ᶠ[𝓝 x] fun y => b i y + (k i j y - ∑ m, θ m y * (p i m y - p j m y)) := by
      filter_upwards [hO] with y hy
      have e := hbG i j y hy
      rw [hG] at e
      linear_combination -e
    have hkD : DifferentiableAt ℂ (k i j) x := (hk i j).differentiableAt hO
    have hdD : ∀ m, DifferentiableAt ℂ (fun y => p i m y - p j m y) x := fun m =>
      (hpD i m x hx.1).sub (hpD j m x hx.2)
    have hmD : ∀ m, DifferentiableAt ℝ (fun y => θ m y * (p i m y - p j m y)) x := fun m =>
      (θ m).differentiableAt.mul ((hdD m).restrictScalars ℝ)
    have hterm : ∀ m, dbar (fun y => θ m y * (p i m y - p j m y)) u x
        = 2 * θ m u * (p i m x - p j m x) := by
      intro m
      rw [dbar_mul (θ m).differentiableAt ((hdD m).restrictScalars ℝ), dbar_anti (θ m) (hθ m),
        dbar_holo (hdD m)]
      ring
    have hsumD : DifferentiableAt ℝ (fun y => ∑ m, θ m y * (p i m y - p j m y)) x :=
      (hasFDerivAt_finset_sum (A := fun m y => θ m y * (p i m y - p j m y)) Finset.univ
        fun m _ => (hmD m).hasFDerivAt).differentiableAt
    have hbj : dbar (b j) u x
        = dbar (b i) u x + (0 - ∑ m, 2 * θ m u * (p i m x - p j m x)) := by
      have hk2 : DifferentiableAt ℝ (fun y => k i j y - ∑ m, θ m y * (p i m y - p j m y)) x :=
        (hkD.restrictScalars ℝ).sub hsumD
      rw [dbar_congr hev, dbar_add (hbD i x hx.1) hk2,
        dbar_sub (hkD.restrictScalars ℝ) hsumD, dbar_holo hkD,
        dbar_sum (f := fun m y => θ m y * (p i m y - p j m y)) Finset.univ fun m _ => hmD m]
      simp only [hterm]
    simp only [hW]
    rw [hbj]
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    ring
  have hWper : ∀ i u (l : Λ), ∀ x ∈ U i, W i u (x + l) = W i u x := by
    intro i u l x hx
    have hev : (fun y => b i (y + l)) =ᶠ[𝓝 x] b i := by
      filter_upwards [(hU i).mem_nhds hx] with y hy using (hb i).2 l y hy
    have hd : dbar (b i) u (x + l) = dbar (b i) u x := by
      rw [← dbar_translate, dbar_congr hev]
    have hi : ∀ m, p i m (x + l) = p i m x - h m l := fun m => hper i m l x hx
    simp only [hW, hd, hi, map_add]
    congr 1
    exact Finset.sum_congr rfl fun m _ => by ring
  have hWd : ∀ i a c, ∀ x ∈ U i,
      dbar (W i a) c x = ∑ m, (2 * θ m a) * (2 * h m c) - dbar (dbar (b i) a) c x := by
    intro i a c x hx
    have hbd1 : DifferentiableAt ℝ (dbar (b i) a) x :=
      (dbar_contDiffAt (hbA i x hx) a).differentiableAt (by norm_num)
    rw [hW, dbar_sub (hSD i a x hx) hbd1,
      dbar_sum (f := fun m y => 2 * θ m a * (p i m y + h m y)) Finset.univ
        fun m _ => hTD i a m x hx]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [dbar_const_mul _ (hPH i m x hx),
      dbar_add ((hpD i m x hx).restrictScalars ℝ) (h m).differentiableAt, dbar_holo (hpD i m x hx),
      dbar_anti (h m) (hh m)]
    ring

  choose ch hch using hcov
  obtain ⟨P, hP⟩ : ∃ P : (Fin g → ℂ) → (Fin g → ℂ) → ℂ, ∀ a z, P a z = W (ch z) a z :=
    ⟨_, fun _ _ => rfl⟩
  have hPloc : ∀ a i, ∀ x ∈ U i, P a =ᶠ[𝓝 x] W i a := by
    intro a i x hx
    filter_upwards [(hU i).mem_nhds hx] with y hy
    rw [hP]
    exact hWeq _ _ a y ⟨hch y, hy⟩
  have hPper : ∀ a (l : Λ) z, P a (z + l) = P a z := by
    intro a l z
    rw [hP, hP, hWeq (ch (z + l)) (ch z) a (z + l) ⟨hch _, hinv _ l z (hch z)⟩,
      hWper _ a l z (hch z)]
  have hPC : ∀ a, ContDiff ℝ 1 (P a) := by
    intro a
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (hWA (ch z) a z (hch z)).congr_of_eventuallyEq (hPloc a (ch z) z (hch z))
  have s1 : ∀ a c, ∑ m, (2 * θ m a) * (2 * h m c) = 4 * ∑ m, θ m a * h m c := by
    intro a c
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have hconst : ∀ z, ∑ n : Fin 4, ![(1 : ℂ), I, -1, -I] n
      * fderiv ℝ (![P u, P u, P v, P v] n) z (![v, I • v, u, I • u] n)
      = 4 * (∑ m, θ m u * h m v - ∑ m, θ m v * h m u) := by
    intro z
    refine Eq.trans (b := dbar (P u) v z - dbar (P v) u z) ?_ ?_
    · simp [Fin.sum_univ_four, dbar]
      ring
    rw [dbar_congr (hPloc u _ z (hch z)), dbar_congr (hPloc v _ z (hch z)),
      hWd _ u v z (hch z), hWd _ v u z (hch z), dbar_symm (hbA _ z (hch z)) u v, s1, s1]
    ring
  have h0 := GlobalTheory.const_eq_zero_of_sum_fderiv_periodic g Λ hd hsp 4 ![P u, P u, P v, P v]
    ![1, I, -1, -I] ![v, I • v, u, I • u] _
    (fun n => ⟨by fin_cases n <;> simp [hPC], fun l z => by fin_cases n <;> simp [hPper]⟩) hconst
  have h4 : (4 : ℂ) ≠ 0 := by norm_num
  exact sub_eq_zero.mp ((mul_eq_zero.mp h0).resolve_left h4)
end GlobalTheory.PeriodSymm
