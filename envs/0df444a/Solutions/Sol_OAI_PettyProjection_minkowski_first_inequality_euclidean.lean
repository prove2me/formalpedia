-- Prove2me | solution 1 for OAI.PettyProjection.minkowski_first_inequality_euclidean
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:10:28.869247+00:00
-- url     : https://prove2.me/submissions/52e4814c-1079-497c-b011-73804dcde09f

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000
import Theorems.Thm_OAI_PettyProjection_brunnMinkowski_classical
import Theorems.Thm_OAI_PettyProjection_brunnMinkowski_equality_euclidean
import Theorems.Thm_OAI_PettyProjection_brunnMinkowski_euclidean

section
-- module Solutions.OAIQW_PettyProjection.BrunnMinkowski
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uF

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

/-- Standard Euclidean volume version used for the projection-body theorem. -/
theorem brunnMinkowski_space {n : ℕ} (hn : 0 < n) : BrunnMinkowskiRoot (Space n) n :=
  brunnMinkowski_euclidean hn

end PettyProjection
end

end OAI
end

section
-- module Solutions.OAIQW_PettyProjection.Homothety
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

lemma volumeRoot_pow {n : ℕ} (hn : 0 < n) (K : Set (Space n)) :
    volumeRoot K^n=volume.real K :=
  Real.rpow_inv_natCast_pow measureReal_nonneg hn.ne'

lemma interior_add_nonempty_left {n : ℕ} {K M : Set (Space n)}
    (hiK : (interior K).Nonempty) (hM : M.Nonempty) : (interior (K+M)).Nonempty := by
  obtain ⟨y,hy⟩ := hM
  obtain ⟨x,hx⟩ := hiK
  refine ⟨x+y,?_⟩
  exact (isOpen_interior.add_right.subset_interior_iff.mpr
    (add_subset_add interior_subset Subset.rfl)) (add_mem_add hx hy)

/-- The homogeneous, additive form of Brunn--Minkowski. -/
theorem brunnMinkowski_add {n : ℕ} (hn : 0 < n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) :
    volumeRoot K+volumeRoot M ≤ volumeRoot (K+M) := by
  have hd : Module.finrank ℝ (Space n) = n := by simp [Space]
  have h := brunnMinkowski_classical (E := Space n) (by rw [hd]; exact hn)
    hK hcK hiK hM hcM hiM
  rw [hd] at h
  exact h

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection

lemma minkowski_parameter_combo {n : ℕ} {K M : Set (Space n)}
    (hcK : Convex ℝ K) (hcM : Convex ℝ M) {s t a b : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a+b=1) :
    a • (K+s • M)+b • (K+t • M)=K+(a*s+b*t) • M := by
  rw [smul_add,smul_add,smul_smul,smul_smul,add_add_add_comm,
    ← hcK.add_smul ha hb,hab,one_smul,← hcM.add_smul (mul_nonneg ha hs) (mul_nonneg hb ht)]

lemma minkowski_volumeRoot_concave {n : ℕ} (hn : 0 < n)
    {K M : Set (Space n)} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hMn : M.Nonempty) : ConcaveOn ℝ (Ici 0) (fun t : ℝ => volumeRoot (K+t • M)) := by
  refine ⟨convex_Ici _,?_⟩
  intro s hs t ht a b ha hb hab
  have hSM : (s • M).Nonempty := hMn.image _
  have hTM : (t • M).Nonempty := hMn.image _
  have h := brunnMinkowski_space hn (K+s • M) (K+t • M)
    (hK.add (hM.smul _)) (hcK.add (hcM.smul _)) (interior_add_nonempty_left hiK hSM)
    (hK.add (hM.smul _)) (hcK.add (hcM.smul _)) (interior_add_nonempty_left hiK hTM) a b ha hb hab
  rw [minkowski_parameter_combo hcK hcM hs ht ha hb hab] at h
  exact h

lemma volumeRoot_diff_factor {n : ℕ} (hn : 0 < n) {K : Set (Space n)}
    (hv : 0 < volume.real K) :
    ((n:ℝ)*volumeRoot K^(n-1))*((n:ℝ)⁻¹*(volume.real K)^((n:ℝ)⁻¹-1))=1 := by
  have hn0 : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Real.rpow_sub hv,Real.rpow_one]
  change (n*volumeRoot K^(n-1))*((n:ℝ)⁻¹*(volumeRoot K/volume.real K))=1
  have hp : volumeRoot K^(n-1)*volumeRoot K=volume.real K := by
    rw [← pow_succ,Nat.sub_add_cancel hn,volumeRoot_pow hn]
  field_simp
  nlinarith [hp]

/-- Minkowski's first inequality in `ℝⁿ` (`EuclideanSpace ℝ (Fin n)`, `n ≥ 2`, Lebesgue
measure), with its equality case: let `K`, `M` be compact convex sets with nonempty interior and
suppose `t ↦ vol(K + t • M)` has derivative `d` at `0` within `[0, ∞)`. Then
`n · (vol(K)^(1/n))^(n-1) · vol(M)^(1/n) ≤ d`, and if equality holds then `K = z + c • M` for
some point `z` and some `c > 0`. -/
theorem minkowski_first_inequality_euclidean_oai {n : ℕ} (hn : 2 ≤ n)
    {K M : Set (EuclideanSpace ℝ (Fin n))} (hK : IsCompact K) (hcK : Convex ℝ K)
    (hiK : (interior K).Nonempty) (hM : IsCompact M) (hcM : Convex ℝ M)
    (hiM : (interior M).Nonempty) {d : ℝ}
    (hd : HasDerivWithinAt (fun t : ℝ => volume.real (K + t • M)) d (Ici 0) 0) :
    (n:ℝ) * (volume.real K ^ ((n:ℝ)⁻¹)) ^ (n - 1) * volume.real M ^ ((n:ℝ)⁻¹) ≤ d ∧
      (d = (n:ℝ) * (volume.real K ^ ((n:ℝ)⁻¹)) ^ (n - 1) * volume.real M ^ ((n:ℝ)⁻¹) →
        ∃ z : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, 0 < c ∧ K = (fun x => z + c • x) '' M) := by
  show (n:ℝ)*volumeRoot K^(n-1)*volumeRoot M ≤ d ∧
      (d=(n:ℝ)*volumeRoot K^(n-1)*volumeRoot M →
        ∃ z : Space n, ∃ c : ℝ, 0 < c ∧ K=(fun x => z+c • x) '' M)
  have hn0 : 0 < n := by omega
  have hnR : 0 < (n:ℝ) := by exact_mod_cast hn0
  have hMn := hiM.mono interior_subset
  have hzero : K+(0:ℝ) • M=K := by simp [zero_smul_set hMn]
  have hvK := volumeReal_pos_of_body hK hiK
  have hf := hd.rpow_const (p := (n:ℝ)⁻¹) (Or.inl (by rw [hzero]; exact hvK.ne'))
  rw [hzero] at hf
  have hc := minkowski_volumeRoot_concave hn0 hK hcK hiK hM hcM hMn
  have hs := hc.slope_le_of_hasDerivWithinAt (by norm_num : (0:ℝ) ∈ Ici 0) (by norm_num : (1:ℝ) ∈ Ici 0)
    (by norm_num : (0:ℝ) < 1) hf
  rw [slope_def_field,hzero,one_smul,sub_zero,div_one] at hs
  have hlow := brunnMinkowski_add hn0 hK hcK hiK hM hcM hiM
  let D : ℝ := n*volumeRoot K^(n-1)
  let C : ℝ := (n:ℝ)⁻¹*(volume.real K)^((n:ℝ)⁻¹-1)
  have hD : 0 < D := mul_pos hnR (pow_pos (volumeRoot_pos hK hiK) _)
  have hDC : D*C=1 := volumeRoot_diff_factor hn0 hvK
  have hs' : D*(volumeRoot (K+M)-volumeRoot K) ≤ d := by
    have he : D*(d*C)=d := by calc
      _ = d*(D*C) := by ring
      _ = d := by rw [hDC,mul_one]
    rw [← he]
    apply mul_le_mul_of_nonneg_left _ hD.le
    simpa only [C,mul_assoc] using hs
  constructor
  · change D*volumeRoot M ≤ d
    exact (mul_le_mul_of_nonneg_left (by linarith : volumeRoot M ≤ volumeRoot (K+M)-volumeRoot K) hD.le).trans hs'
  · intro heq
    have hv : volumeRoot (K+M)=volumeRoot K+volumeRoot M := by
      change d=D*volumeRoot M at heq
      rw [heq] at hs'
      have ht := (mul_le_mul_iff_right₀ hD).mp hs'
      linarith
    exact brunnMinkowski_equality_euclidean hn hK hcK hiK hM hcM hiM hv

end PettyProjection
end

end OAI
end

theorem solution : type_of% @OAI.PettyProjection.minkowski_first_inequality_euclidean_oai := @OAI.PettyProjection.minkowski_first_inequality_euclidean_oai
