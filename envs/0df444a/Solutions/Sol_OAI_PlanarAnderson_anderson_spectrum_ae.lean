-- Prove2me | solution 1 for OAI.PlanarAnderson.anderson_spectrum_ae
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:26:55.025407+00:00
-- url     : https://prove2.me/submissions/09b01781-9c49-48e0-ad08-3a67c02ea3d4

-- Generated from openai/math@1581d4c lean/OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean:L678-L683
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.PlanarAnderson.anderson_spectrum_ae.
-- The statement is the platform stub (Theorems.Thm_OAI_PlanarAnderson_anderson_spectrum_ae) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_PlanarAndersonSpectrum
import Definitions.Def_OAI_MathematicalPhysics_PlanarAnderson_Spectrum

-- ---- inline helpers from OAI.MathematicalPhysics.PlanarAnderson.Spectrum ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

/-! The nearest-neighbor Anderson operator on the square lattice and its almost-sure spectral interval. -/

noncomputable section
open MeasureTheory
open scoped ENNReal

namespace PlanarAnderson
 theorem inner_permute (e : Site ≃ Site) (u w : Hilbert) :
    inner ℂ (permute e u) w = inner ℂ u (permute e.symm w) := by
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  conv_rhs => rw [← e.tsum_eq (fun x => inner ℂ (u x) (permute e.symm w x))]
  simp

 theorem norm_hopping_le : ‖hopping‖ ≤ 4 := by
  have he (a : Site) : ‖(permute (translation a)).toContinuousLinearMap‖ ≤ 1 :=
    LinearIsometry.norm_toContinuousLinearMap_le _
  have h1 := norm_add_le
    (permute (translation (1, 0))).toContinuousLinearMap
    (permute (translation (-1, 0))).toContinuousLinearMap
  have h2 := norm_add_le
    ((permute (translation (1, 0))).toContinuousLinearMap +
      (permute (translation (-1, 0))).toContinuousLinearMap)
    (permute (translation (0, 1))).toContinuousLinearMap
  have h3 := norm_add_le
    ((permute (translation (1, 0))).toContinuousLinearMap +
      (permute (translation (-1, 0))).toContinuousLinearMap +
      (permute (translation (0, 1))).toContinuousLinearMap)
    (permute (translation (0, -1))).toContinuousLinearMap
  dsimp [hopping]
  linarith [he (1, 0), he (-1, 0), he (0, 1), he (0, -1)]

 theorem translation_symm (a : Site) : (translation a).symm = translation (-a) := by
   apply Equiv.ext
   intro x
   change x - a = x + -a
   exact sub_eq_add_neg x a

 theorem hopping_selfAdjoint : IsSelfAdjoint hopping := by
   apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
   intro u w
   change inner ℂ (hopping u) w = inner ℂ u (hopping w)
   simp only [hopping, add_apply, inner_add_left, inner_add_right,
     LinearIsometry.coe_toContinuousLinearMap, inner_permute, translation_symm]
   simp only [Prod.neg_mk, neg_neg, neg_zero]
   ring

 theorem norm_potential_le (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) : ‖potential v hh hv‖ ≤ h :=
   lp.norm_mapCLM_le _ _ _ _

 theorem potential_selfAdjoint (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) : IsSelfAdjoint (potential v hh hv) := by
   apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
   intro u w
   change inner ℂ (potential v hh hv u) w = inner ℂ u (potential v hh hv w)
   rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
   congr 1
   funext x
   simp [RCLike.inner_apply, mul_left_comm, mul_assoc]

 theorem anderson_formula (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) : IsAndersonOperator v (anderson v hh hv) := by
   intro u x
   simp [anderson]

 theorem anderson_selfAdjoint (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) : IsSelfAdjoint (anderson v hh hv) := by
   change IsSelfAdjoint (hopping + potential v hh hv)
   exact IsSelfAdjoint.add (R := Hilbert →L[ℂ] Hilbert)
     hopping_selfAdjoint (potential_selfAdjoint v hh hv)

 theorem norm_anderson_le (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) : ‖anderson v hh hv‖ ≤ 4 + h :=
   (norm_add_le _ _).trans (add_le_add norm_hopping_le (norm_potential_le v hh hv))

 theorem spectrum_subset (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) : spectrum ℂ (anderson v hh hv) ⊆ spectralInterval h := by
   intro z hz
   have hr := (anderson_selfAdjoint v hh hv).im_eq_zero_of_mem_spectrum hz
   have hn := (spectrum.norm_le_norm_of_mem hz).trans (norm_anderson_le v hh hv)
   refine ⟨hr, ?_, ?_⟩
   · have : -z.re ≤ ‖z‖ := by simpa using Complex.re_le_norm (-z)
     linarith
   · exact (Complex.re_le_norm z).trans hn

theorem uniform_probability {h : ℝ} (hh : 0 < h) :
    IsProbabilityMeasure (ProbabilityTheory.cond volume (Set.Icc (-h) h)) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure_of_finite
  · rw [Real.volume_Icc]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (by linarith))
  · rw [Real.volume_Icc]
    exact ENNReal.ofReal_ne_top

 theorem bounded_ae {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∀ x, |v x| ≤ h := by
  let := uniform_probability hh
  rw [ae_all_iff]
  intro x
  have he := (measurePreserving_eval_infinitePi
    (fun _ : Site => ProbabilityTheory.cond volume (Set.Icc (-h) h)) x).quasiMeasurePreserving.ae (ProbabilityTheory.ae_cond_mem measurableSet_Icc)
  filter_upwards [he] with v hv
  exact abs_le.mpr hv

 theorem plane_norm {q : ℂ} (hq : ‖q‖ = 1) (x : Site) : ‖plane q x‖ = 1 := by
  simp [plane, norm_zpow, hq]

 theorem cube_card (n : ℕ) : (cube n).card = (n + 1) ^ 2 := by
  simp [cube, Finset.card_product, Int.card_Icc, pow_two]

 theorem cutWave_norm {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) :
    ‖cutWave q n‖ = n + 1 := by
  have hsq : ‖cutWave q n‖ ^ 2 = ((n : ℝ) + 1) ^ 2 := by
    have hs := lp.norm_sum_single (E := fun _ : Site => ℂ) (p := 2)
      (by norm_num) (plane q) (cube n)
    norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at hs
    rw [show (∑ x ∈ cube n, ‖plane q x‖ ^ (2 : ℕ)) = (cube n).card by
      simp [plane_norm hq]] at hs
    simpa [cutWave, cube_card] using hs
  nlinarith [norm_nonneg (cutWave q n), (show (0 : ℝ) ≤ n by positivity)]

 theorem cutWave_point_bound {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) (x : Site) :
    ‖cutWave q n x‖ ≤ 1 := by
  rw [cutWave_apply]
  split <;> simp [plane_norm hq]

 theorem freeEnergy_norm_le {q : ℂ} (hq : ‖q‖ = 1) : ‖freeEnergy q‖ ≤ 4 := by
  dsimp [freeEnergy]
  rw [norm_mul]
  norm_num
  have hi : ‖q + q⁻¹‖ ≤ 2 := by simpa only [hq, norm_inv, inv_one, one_add_one_eq_two] using norm_add_le q q⁻¹
  linarith

 theorem plane_hopping {q : ℂ} (hq : q ≠ 0) (x : Site) :
    plane q (x.1 + 1, x.2) + plane q (x.1 - 1, x.2) +
      plane q (x.1, x.2 + 1) + plane q (x.1, x.2 - 1) = freeEnergy q * plane q x := by
  have e1 : x.1 + 1 + x.2 = (x.1 + x.2) + 1 := by omega
  have e2 : x.1 - 1 + x.2 = (x.1 + x.2) + (-1) := by omega
  have e3 : x.1 + (x.2 + 1) = (x.1 + x.2) + 1 := by omega
  have e4 : x.1 + (x.2 - 1) = (x.1 + x.2) + (-1) := by omega
  simp only [plane, freeEnergy, e1, e2, e3, e4, zpow_add₀ hq, zpow_one, zpow_neg_one]
  ring

 theorem free_error_inner {q : ℂ} (hq : q ≠ 0) (n : ℕ) (x : Site)
    (hx : x ∈ innerCube n) :
    (hopping (cutWave q n) - freeEnergy q • cutWave q n) x = 0 := by
  simp only [innerCube, Finset.mem_product, Finset.mem_Icc] at hx
  have h0 : x ∈ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h1 : (x.1 + 1, x.2) ∈ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h2 : (x.1 - 1, x.2) ∈ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h3 : (x.1, x.2 + 1) ∈ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h4 : (x.1, x.2 - 1) ∈ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    hopping_apply, cutWave_apply, ite_eq_left h0, ite_eq_left h1, ite_eq_left h2,
    ite_eq_left h3, ite_eq_left h4]
  exact sub_eq_zero.mpr (plane_hopping hq x)

 theorem free_error_outer (q : ℂ) (n : ℕ) (x : Site) (hx : x ∉ outerCube n) :
    (hopping (cutWave q n) - freeEnergy q • cutWave q n) x = 0 := by
  simp only [outerCube, Finset.mem_product, Finset.mem_Icc, not_and] at hx
  have h0 : x ∉ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h1 : (x.1 + 1, x.2) ∉ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h2 : (x.1 - 1, x.2) ∉ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h3 : (x.1, x.2 + 1) ∉ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  have h4 : (x.1, x.2 - 1) ∉ cube n := by simp [cube, Finset.mem_product, Finset.mem_Icc]; omega
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    hopping_apply, cutWave_apply, ite_eq_right h0, ite_eq_right h1, ite_eq_right h2,
    ite_eq_right h3, ite_eq_right h4]
  simp

 theorem boundary_card (n : ℕ) (hn : 1 ≤ n) : (boundary n).card = 8 * (n + 1) := by
  have hi : innerCube n ⊆ outerCube n := by
    intro x hx
    simp only [innerCube, outerCube, Finset.mem_product, Finset.mem_Icc] at hx ⊢
    omega
  rw [boundary, Finset.card_sdiff_of_subset hi]
  have ho : (outerCube n).card = (n + 3)^2 := by
    simp only [outerCube, Finset.card_product, Int.card_Icc]
    have : (↑n + 1 + 1 - (-1) : ℤ).toNat = n + 3 := by omega
    rw [this, pow_two]
  have hj : (innerCube n).card = (n - 1)^2 := by
    simp only [innerCube, Finset.card_product, Int.card_Icc]
    have : (↑n - 1 + 1 - 1 : ℤ).toNat = n - 1 := by omega
    rw [this, pow_two]
  rw [ho, hj]
  have : (n + 3)^2 = (n - 1)^2 + 8 * (n + 1) := by
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simp only [Nat.add_sub_cancel_left]
    ring
  omega

 theorem free_error_point_bound {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) (x : Site) :
    ‖(hopping (cutWave q n) - freeEnergy q • cutWave q n) x‖ ≤ 8 := by
  simp only [lp.coeFn_sub, Pi.sub_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    hopping_apply]
  calc
    _ ≤ ‖cutWave q n (x.1+1,x.2)‖ + ‖cutWave q n (x.1-1,x.2)‖ +
      ‖cutWave q n (x.1,x.2+1)‖ + ‖cutWave q n (x.1,x.2-1)‖ +
      ‖freeEnergy q‖ * ‖cutWave q n x‖ := by
        grw [norm_sub_le, norm_add_le, norm_add_le, norm_add_le, norm_mul]
    _ ≤ 8 := by
      have hm := mul_le_mul (freeEnergy_norm_le hq) (cutWave_point_bound hq n x)
        (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 4)
      linarith [cutWave_point_bound hq n (x.1+1,x.2),
        cutWave_point_bound hq n (x.1-1,x.2), cutWave_point_bound hq n (x.1,x.2+1),
        cutWave_point_bound hq n (x.1,x.2-1)]

 theorem finite_norm_sq (u : Hilbert) (s : Finset Site) (hu : ∀ x ∉ s, u x = 0) :
    ‖u‖^2 = ∑ x ∈ s, ‖u x‖^2 := by
  have he := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) u
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_two] at he
  rw [he]
  apply tsum_eq_sum
  intro x hx
  simp [hu x hx]

 theorem free_error_norm_sq {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) (hn : 1 ≤ n) :
    ‖hopping (cutWave q n) - freeEnergy q • cutWave q n‖^2 ≤ 512 * ((n:ℝ)+1) := by
  have hq0 : q ≠ 0 := by intro he; simp [he] at hq
  have hs : ∀ x ∉ boundary n, (hopping (cutWave q n) - freeEnergy q • cutWave q n) x = 0 := by
    intro x hx
    by_cases ho : x ∈ outerCube n
    · have hi : x ∈ innerCube n := by simpa [boundary, ho] using hx
      exact free_error_inner hq0 n x hi
    · exact free_error_outer q n x ho
  rw [finite_norm_sq _ (boundary n) hs]
  calc
    _ ≤ ∑ _x ∈ boundary n, (64:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      have hb := free_error_point_bound hq n x
      nlinarith [norm_nonneg ((hopping (cutWave q n) - freeEnergy q • cutWave q n) x)]
    _ = _ := by simp [boundary_card n hn]; ring

 theorem free_error_relative {q : ℂ} (hq : ‖q‖ = 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ n : ℕ, 1 ≤ n ∧ ‖hopping (cutWave q n) - freeEnergy q • cutWave q n‖ ≤
      δ * ‖cutWave q n‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt (512 / δ^2)
  let n := k + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  refine ⟨n, hn, ?_⟩
  rw [cutWave_norm hq]
  have hδ2 : 0 < δ^2 := sq_pos_of_pos hδ
  have hk' : 512 < (k:ℝ) * δ^2 := (div_lt_iff₀ hδ2).mp hk
  have hb := free_error_norm_sq hq n hn
  have hn0 : 0 < (n:ℝ)+1 := by positivity
  have hn1 : (k:ℝ) < (n:ℝ)+1 := by dsimp [n]; push_cast; linarith
  have hx : 512 ≤ δ^2 * ((n:ℝ)+1) := by nlinarith
  have hy := mul_le_mul_of_nonneg_right hx hn0.le
  have hz : 0 ≤ δ * ((n:ℝ)+1) := by positivity
  nlinarith [norm_nonneg (hopping (cutWave q n) - freeEnergy q • cutWave q n)]

 theorem diagonal_error_bound (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) (w ε : ℝ)
    (hε : 0 ≤ ε) (hclose : ∀ x ∈ cube n, |v x - w| ≤ ε) :
    ‖potential v hh hv (cutWave q n) - (w:ℂ) • cutWave q n‖ ≤ ε * ((n:ℝ)+1) := by
  let u := potential v hh hv (cutWave q n) - (w:ℂ) • cutWave q n
  have hu (x : Site) : u x = ((v x - w : ℝ):ℂ) * cutWave q n x := by
    simp only [u, lp.coeFn_sub, Pi.sub_apply, potential_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul, Complex.ofReal_sub]
    ring
  have hout : ∀ x ∉ cube n, u x = 0 := by
    intro x hx
    simp [hu, hx]
  have hsq : ‖u‖^2 ≤ ε^2 * ((n:ℝ)+1)^2 := by
    rw [finite_norm_sq u (cube n) hout]
    calc
      _ ≤ ∑ _x ∈ cube n, ε^2 := by
        apply Finset.sum_le_sum
        intro x hx
        have hp : ‖u x‖ ≤ ε := by
          rw [hu, norm_mul, cutWave_apply, ite_eq_left hx, plane_norm hq, mul_one,
            Complex.norm_real, Real.norm_eq_abs]
          exact hclose x hx
        nlinarith [norm_nonneg (u x)]
      _ = _ := by simp [cube_card]; ring
  change ‖u‖ ≤ _
  nlinarith [norm_nonneg u, (show 0 ≤ ε * ((n:ℝ)+1) by positivity)]

 theorem anderson_shift (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) (u : Hilbert) (t : Site) :
    anderson v hh hv (permute (translation (-t)) u) =
      permute (translation (-t))
        (anderson (fun x => v (x+t)) hh (fun x => hv (x+t)) u) := by
  ext x
  simp [anderson, hopping_apply, permute_apply, translation_apply, Prod.add_def,
    sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

 theorem constant_box_relative (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) {q : ℂ} (hq : ‖q‖ = 1) (n : ℕ) (w : ℝ) {δ : ℝ}
    (hδ : 0 < δ) (t : Site)
    (hfree : ‖hopping (cutWave q n) - freeEnergy q • cutWave q n‖ ≤ δ * ‖cutWave q n‖)
    (hclose : ∀ x ∈ cube n, |v (x+t) - w| ≤ δ) :
    ∃ u : Hilbert, 0 < ‖u‖ ∧
      ‖anderson v hh hv u - (freeEnergy q + (w:ℂ)) • u‖ ≤ (2*δ) * ‖u‖ := by
  let P := permute (translation (-t))
  let u := P (cutWave q n)
  have hun : ‖u‖ = (n:ℝ)+1 := by dsimp [u]; rw [P.norm_map, cutWave_norm hq]
  refine ⟨u, by rw [hun]; positivity, ?_⟩
  have he : anderson v hh hv u - (freeEnergy q + (w:ℂ)) • u =
    P ((hopping (cutWave q n) - freeEnergy q • cutWave q n) +
      (potential (fun x => v (x+t)) hh (fun x => hv (x+t)) (cutWave q n) -
        (w:ℂ) • cutWave q n)) := by
    dsimp only [u]
    rw [anderson_shift]
    simp only [P, map_add, map_sub, map_smul, anderson, add_apply,
      add_smul]
    abel
  rw [he, P.norm_map, hun]
  have hb := diagonal_error_bound (fun x => v (x+t)) hh (fun x => hv (x+t)) hq n w δ
    hδ.le hclose
  rw [cutWave_norm hq] at hfree
  exact (norm_add_le _ _).trans (by linarith)

 theorem spectrum_of_approximate (H : Hilbert →L[ℂ] Hilbert) (z : ℂ)
    (hap : ∀ ε : ℝ, 0 < ε → ∃ u : Hilbert, 0 < ‖u‖ ∧ ‖H u - z • u‖ ≤ ε * ‖u‖) :
    z ∈ spectrum ℂ H := by
  apply spectrum.mem_iff.mpr
  intro hi
  let B : Hilbert →L[ℂ] Hilbert := ↑hi.unit⁻¹
  have hB : B * (algebraMap ℂ (Hilbert →L[ℂ] Hilbert) z - H) = 1 := by
    exact hi.val_inv_mul
  have hrec (u : Hilbert) : B (z • u - H u) = u := by
    have he := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A u) hB
    simpa only [mul_apply_eq_comp, sub_apply,
      ContinuousLinearMap.algebraMap_apply, one_apply_eq_self] using he
  let C : ℝ := ‖B‖ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  let ε : ℝ := 1 / (2 * C)
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hmul : C * ε = 1/2 := by dsimp [ε]; field_simp
  obtain ⟨u, hu, he⟩ := hap ε hε
  have hb : ‖u‖ ≤ ‖B‖ * ‖H u - z • u‖ := by
    calc
      _ = ‖B (z • u - H u)‖ := congrArg norm (hrec u).symm
      _ ≤ ‖B‖ * ‖z • u - H u‖ := B.le_opNorm _
      _ = _ := by rw [norm_sub_rev]
  have hc : ‖B‖ * ‖H u - z • u‖ ≤ C * (ε * ‖u‖) :=
    mul_le_mul (by dsimp [C]; linarith) he (norm_nonneg _) hC.le
  rw [← mul_assoc, hmul] at hc
  linarith

 theorem freeEnergy_surjective {e : ℝ} (he : e ∈ Set.Icc (-4:ℝ) 4) :
    ∃ q : ℂ, ‖q‖ = 1 ∧ freeEnergy q = (e:ℂ) := by
  have ht : e/4 ∈ Set.range Real.cos := by
    rw [Real.range_cos]
    constructor <;> linarith [he.1, he.2]
  obtain ⟨k, hk⟩ := ht
  refine ⟨Complex.exp ((k:ℂ)*Complex.I), Complex.norm_exp_ofReal_mul_I k, ?_⟩
  dsimp [freeEnergy]
  rw [← Complex.exp_neg]
  have hneg : -((k:ℂ)*Complex.I) = ((-k:ℝ):ℂ)*Complex.I := by push_cast; ring
  rw [hneg, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
  rw [hk]
  push_cast
  ring

theorem iid_exists_ae {X : Type*} [MeasurableSpace X] (μ : Measure X)
    [IsProbabilityMeasure μ] {s : Set X} (hs : MeasurableSet s) (hp : μ s ≠ 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => μ), ∃ n, ω n ∈ s := by
  rw [ae_iff]
  have hn (n : ℕ) : Measure.infinitePi (fun _ : ℕ => μ)
      {ω | ¬ ∃ n, ω n ∈ s} ≤ (μ sᶜ) ^ n := by
    calc
      _ ≤ Measure.infinitePi (fun _ : ℕ => μ)
          (Set.pi (Finset.range n) (fun _ => sᶜ)) := measure_mono (by
            intro ω hω i hi
            exact fun his => hω ⟨i, his⟩)
      _ = (μ sᶜ) ^ n := by
        rw [Measure.infinitePi_pi _ (fun _ _ => hs.compl)]
        simp
  have hlt : μ sᶜ < 1 := by
    rw [measure_compl hs (measure_ne_top μ s), measure_univ]
    exact ENNReal.sub_lt_self (by simp) (by simp) hp
  exact le_antisymm
    (le_of_tendsto_of_tendsto' tendsto_const_nhds
      (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt) hn) zero_le

theorem trialSite_injective (n : ℕ) :
    Function.Injective (fun kp : ℕ × Patch n => trialSite n kp.1 kp.2) := by
  rintro ⟨k, a, b⟩ ⟨l, c, d⟩ he
  have h1 : k * (n + 1) + a.val = l * (n + 1) + c.val := by
    have ht := congrArg Prod.fst he
    dsimp [trialSite] at ht
    exact_mod_cast ht
  have h2 : b.val = d.val := by
    have ht := congrArg Prod.snd he
    dsimp [trialSite] at ht
    exact_mod_cast ht
  have hk : k = l := by
    have hh := congrArg (fun z => z / (n + 1)) h1
    rw [Nat.mul_comm k, Nat.mul_comm l, Nat.mul_add_div (Nat.succ_pos _),
      Nat.mul_add_div (Nat.succ_pos _)] at hh
    simpa only [Nat.div_eq_of_lt a.isLt, Nat.div_eq_of_lt c.isLt, Nat.add_zero] using hh
  have ha : a = c := by
    apply Fin.ext
    rw [hk] at h1
    exact Nat.add_left_cancel h1
  have hb : b = d := Fin.ext h2
  simp [hk, ha, hb]

theorem trial_law {h : ℝ} (hh : 0 < h) (n : ℕ) :
    (disorderLaw h).map (fun v k p => v (trialSite n k p)) =
      Measure.infinitePi (fun _ : ℕ => Measure.infinitePi
        (fun _ : Patch n => ProbabilityTheory.cond volume (Set.Icc (-h) h))) := by
  let := uniform_probability hh
  have hm := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Site => ProbabilityTheory.cond volume (Set.Icc (-h) h))
    (trialSite_injective n)
  have hc := Measure.infinitePi_map_curry
    (fun (_ : ℕ) (_ : Patch n) => ProbabilityTheory.cond volume (Set.Icc (-h) h))
  rw [← hc, ← hm]
  rw [Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem uniform_interval_pos {h w ε : ℝ} (hw : w ∈ Set.Ioo (-h) h) (hε : 0 < ε) :
    0 < (ProbabilityTheory.cond volume (Set.Icc (-h) h))
      (Set.Ioo (w - ε) (w + ε)) := by
  rw [ProbabilityTheory.cond_apply measurableSet_Icc]
  apply ENNReal.mul_pos
  · rw [ENNReal.inv_ne_zero, Real.volume_Icc]
    exact ENNReal.ofReal_ne_top
  · apply ne_of_gt
    apply lt_of_lt_of_le
      ((isOpen_Ioo.inter isOpen_Ioo).measure_pos volume
        (show (Set.Ioo (-h) h ∩ Set.Ioo (w - ε) (w + ε)).Nonempty from
          ⟨w, hw, by constructor <;> linarith⟩))
    apply measure_mono
    exact Set.inter_subset_inter_left _ Set.Ioo_subset_Icc_self

theorem constant_trial_ae {h w ε : ℝ} (hh : 0 < h)
    (hw : w ∈ Set.Ioo (-h) h) (hε : 0 < ε) (n : ℕ) :
    ∀ᵐ v ∂disorderLaw h, ∃ k : ℕ, ∀ p : Patch n,
      |v (trialSite n k p) - w| < ε := by
  let := uniform_probability hh
  let μ := ProbabilityTheory.cond volume (Set.Icc (-h) h)
  let s : Set (Patch n → ℝ) := Set.univ.pi (fun _ => Set.Ioo (w - ε) (w + ε))
  have hs : MeasurableSet s := MeasurableSet.pi (Set.to_countable _) (by measurability)
  have hp : (Measure.infinitePi (fun _ : Patch n => μ)) s ≠ 0 := by
    dsimp [s]
    rw [Measure.infinitePi_pi_univ _ (fun _ => measurableSet_Ioo), tprod_fintype]
    exact Finset.prod_ne_zero_iff.mpr (fun _ _ => ne_of_gt (uniform_interval_pos hw hε))
  have he := iid_exists_ae (Measure.infinitePi (fun _ : Patch n => μ)) hs hp
  have hm : MeasurePreserving (fun v k p => v (trialSite n k p))
      (disorderLaw h) (Measure.infinitePi (fun _ : ℕ =>
        Measure.infinitePi (fun _ : Patch n => μ))) :=
    ⟨by fun_prop, trial_law hh n⟩
  filter_upwards [hm.quasiMeasurePreserving.ae he] with v hv
  obtain ⟨k, hk⟩ := hv
  refine ⟨k, fun p => ?_⟩
  have hp := hk p (Set.mem_univ p)
  exact abs_lt.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩

theorem constant_boxes_ae {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, HasConstantBoxes v h := by
  have he : ∀ᵐ v ∂disorderLaw h, ∀ (q : ℚ) (l n : ℕ),
      (q : ℝ) ∈ Set.Ioo (-h) h → ∃ k : ℕ,
        ∀ p : Patch n, |v (trialSite n k p) - (q : ℝ)| < 1 / ((l : ℝ) + 1) := by
    simp only [ae_all_iff]
    intro q l n
    by_cases hq : (q : ℝ) ∈ Set.Ioo (-h) h
    · intro _
      exact constant_trial_ae hh hq (by positivity) n
    · simp [hq]
  filter_upwards [he] with v hv
  intro w hw ε hε n
  let δ := min (ε / 2) (min (w + h) (h - w))
  have hδ : 0 < δ := by dsimp [δ]; exact lt_min (by linarith) (lt_min (by linarith [hw.1]) (by linarith [hw.2]))
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show w - δ < w + δ by linarith)
  have hd1 : δ ≤ ε / 2 := min_le_left _ _
  have hd2 : δ ≤ w + h := (min_le_right _ _).trans (min_le_left _ _)
  have hd3 : δ ≤ h - w := (min_le_right _ _).trans (min_le_right _ _)
  have hq : (q : ℝ) ∈ Set.Ioo (-h) h := ⟨by linarith, by linarith⟩
  have hwq : |(q : ℝ) - w| < ε / 2 := abs_lt.mpr ⟨by linarith, by linarith⟩
  obtain ⟨l, hl⟩ := exists_nat_one_div_lt (show 0 < ε / 2 by linarith)
  obtain ⟨k, hk⟩ := hv q l n hq
  refine ⟨(((k * (n + 1) : ℕ) : ℤ), 0), fun p => ?_⟩
  have hsite : patchSite n p + (((k * (n + 1) : ℕ) : ℤ), 0) = trialSite n k p := by
    ext <;> simp [patchSite, trialSite, Nat.cast_add, add_comm]
  rw [hsite]
  calc
    |v (trialSite n k p) - w| =
      |(v (trialSite n k p) - (q : ℝ)) + ((q : ℝ) - w)| := by congr 1; ring
    _ ≤ |v (trialSite n k p) - (q : ℝ)| + |(q : ℝ) - w| := abs_add_le _ _
    _ < ε := by linarith [hk p]

theorem cube_is_patch (n : ℕ) (x : Site) (hx : x ∈ cube n) :
    ∃ p : Patch n, patchSite n p = x := by
  simp only [cube, Finset.mem_product, Finset.mem_Icc] at hx
  refine ⟨(⟨x.1.toNat, by omega⟩, ⟨x.2.toNat, by omega⟩), ?_⟩
  ext <;> simp only [patchSite, Int.toNat_of_nonneg, hx.1.1, hx.2.1]

theorem spectrum_contains_shifted_free (v : Configuration) {h : ℝ} (hh : 0 ≤ h)
    (hv : ∀ x, |v x| ≤ h) (hbox : HasConstantBoxes v h) {w : ℝ}
    (hw : w ∈ Set.Ioo (-h) h) {q : ℂ} (hq : ‖q‖ = 1) :
    freeEnergy q + (w:ℂ) ∈ spectrum ℂ (anderson v hh hv) := by
  apply spectrum_of_approximate
  intro ε hε
  have hd : 0 < ε/2 := by linarith
  obtain ⟨n, hn, hfree⟩ := free_error_relative hq hd
  obtain ⟨t, ht⟩ := hbox w hw (ε/2) hd n
  have hc : ∀ x ∈ cube n, |v (x+t) - w| ≤ ε/2 := by
    intro x hx
    obtain ⟨p, rfl⟩ := cube_is_patch n x hx
    exact (ht p).le
  obtain ⟨u, hu, he⟩ := constant_box_relative v hh hv hq n w hd t hfree hc
  exact ⟨u, hu, by convert he using 1; ring⟩

theorem spectrum_contains_interior (v : Configuration) {h : ℝ} (hh : 0 < h)
    (hv : ∀ x, |v x| ≤ h) (hbox : HasConstantBoxes v h) {e : ℝ}
    (he : e ∈ Set.Ioo (-4-h) (4+h)) :
    (e:ℂ) ∈ spectrum ℂ (anderson v hh.le hv) := by
  let a := e/(4+h)
  have hp : 0 < 4+h := by linarith
  have hlo : -1 < a := by change -1 < e/(4+h); apply (lt_div_iff₀ hp).mpr; linarith [he.1]
  have hhi : a < 1 := by change e/(4+h) < 1; apply (div_lt_iff₀ hp).mpr; linarith [he.2]
  have hw : h*a ∈ Set.Ioo (-h) h := by
    constructor
    · nlinarith
    · nlinarith
  have hf : 4*a ∈ Set.Icc (-4:ℝ) 4 := ⟨by linarith, by linarith⟩
  obtain ⟨q, hq, hqe⟩ := freeEnergy_surjective hf
  have hm := spectrum_contains_shifted_free v hh.le hv hbox hw hq
  have hea : (4+h)*a = e := by dsimp [a]; field_simp
  have hec : freeEnergy q + ((h*a:ℝ):ℂ) = (e:ℂ) := by
    rw [hqe, ← Complex.ofReal_add]
    congr 1
    nlinarith
  rwa [hec] at hm

theorem spectrum_eq_interval (v : Configuration) {h : ℝ} (hh : 0 < h)
    (hv : ∀ x, |v x| ≤ h) (hbox : HasConstantBoxes v h) :
    spectrum ℂ (anderson v hh.le hv) = spectralInterval h := by
  apply Set.Subset.antisymm (spectrum_subset v hh.le hv)
  have hi : Set.Ioo (-4-h) (4+h) ⊆ Complex.ofReal ⁻¹' spectrum ℂ (anderson v hh.le hv) := by
    intro e he
    exact spectrum_contains_interior v hh hv hbox he
  have hc := closure_minimal hi ((spectrum.isClosed (𝕜 := ℂ) (anderson v hh.le hv)).preimage
    Complex.continuous_ofReal)
  rw [closure_Ioo (by linarith : -4-h ≠ 4+h)] at hc
  intro z hz
  have hm := hc ⟨hz.2.1, hz.2.2⟩
  have hez : (z.re:ℂ) = z := by apply Complex.ext <;> simp [hz.1]
  simpa only [Set.mem_preimage, hez] using hm

end PlanarAnderson

end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.PlanarAnderson
open MeasureTheory
open scoped ENNReal

theorem solution {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h := by
  filter_upwards [bounded_ae hh, constant_boxes_ae hh] with v hv hbox
  exact ⟨anderson v hh.le hv, anderson_formula v hh.le hv,
    anderson_selfAdjoint v hh.le hv, spectrum_eq_interval v hh hv hbox⟩
