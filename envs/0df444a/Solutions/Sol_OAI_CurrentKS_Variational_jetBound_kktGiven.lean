-- Prove2me | solution 1 for OAI.CurrentKS.Variational.jetBound_kktGiven
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T22:57:10.401029+00:00
-- url     : https://prove2.me/submissions/81a8ef19-4b56-4e34-af2e-ee960c2969be

import Mathlib
import Definitions.Def_OAIQ241TT006

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_BilinearIteratedBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open Filter Set
open scoped Topology

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma bilinear_iterated_bound (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} {n : ℕ} (hf : ContDiffAt ℝ n f x) (hg : ContDiffAt ℝ n g x)
    (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ n (fun y => B (f y) (g y)) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i f x‖ * ‖iteratedFDeriv ℝ (n-i) g x‖ := by
  obtain ⟨u,hu,hxu,hfu⟩ := hf.contDiffOn' le_rfl (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  obtain ⟨v,hv,hxv,hgv⟩ := hg.contDiffOn' le_rfl (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  let s := u ∩ v
  have hs : IsOpen s := hu.inter hv
  have hx : x ∈ s := ⟨hxu,hxv⟩
  have hfs : ContDiffOn ℝ n f s := (by simpa using hfu : ContDiffOn ℝ n f u).mono inter_subset_left
  have hgs : ContDiffOn ℝ n g s := (by simpa using hgv : ContDiffOn ℝ n g v).mono inter_subset_right
  have hb := B.norm_iteratedFDerivWithin_le_of_bilinear_of_le_one
    hfs hgs hs.uniqueDiffOn hx (le_refl (n : WithTop ℕ∞)) hB
  have hres : ContDiffAt ℝ n (fun y => B (f y) (g y)) x := B.isBoundedBilinearMap.contDiff.comp_contDiffAt x (hf.prodMk hg)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn hres hx] at hb
  convert hb using 1
  all_goals try with_reducible_and_instances rfl
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hf.of_le (by exact_mod_cast hi')) hx,
    iteratedFDerivWithin_eq_iteratedFDeriv hs.uniqueDiffOn (hg.of_le (by exact_mod_cast Nat.sub_le n i)) hx]

variable {R : Type*} [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

lemma contDiffAt_inverse_of_unit {x : R} (hx : IsUnit x) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (@Ring.inverse R _) x := by
  obtain ⟨x,rfl⟩ := hx
  exact contDiffAt_ringInverse ℝ x

lemma fderiv_inverse_eq {x : R} (hx : IsUnit x) :
    fderiv ℝ (@Ring.inverse R _) x =
      -ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse x) (Ring.inverse x) := by
  obtain ⟨x,rfl⟩ := hx
  simpa only [Ring.inverse_unit] using fderiv_inverse (𝕜 := ℝ) x

lemma inverse_succ_bound {x : R} (hx : IsUnit x) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n+1) (@Ring.inverse R _) x‖ ≤
      ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i (@Ring.inverse R _) x‖ *
        ‖iteratedFDeriv ℝ (n-i) (@Ring.inverse R _) x‖ := by
  have he : fderiv ℝ (@Ring.inverse R _) =ᶠ[𝓝 x]
      fun y => -ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse y) (Ring.inverse y) := by
    filter_upwards [Units.isOpen.mem_nhds hx] with y hy
    exact fderiv_inverse_eq hy
  have he' : fderiv ℝ (@Ring.inverse R _) =ᶠ[𝓝 x]
      -(fun y => ContinuousLinearMap.mulLeftRight ℝ R (Ring.inverse y) (Ring.inverse y)) := by
    exact he
  rw [← norm_iteratedFDeriv_fderiv, (he'.iteratedFDeriv ℝ n).eq_of_nhds,
    iteratedFDeriv_neg_apply, norm_neg]
  exact bilinear_iterated_bound _ (contDiffAt_inverse_of_unit hx)
    (contDiffAt_inverse_of_unit hx) (ContinuousLinearMap.opNorm_mulLeftRight_le ℝ R)

theorem inverse_first_three {x : R} (hx : IsUnit x) :
    ‖fderiv ℝ (@Ring.inverse R _) x‖ ≤ ‖Ring.inverse x‖^2 ∧
    ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ ≤ 2*‖Ring.inverse x‖^3 ∧
    ‖iteratedFDeriv ℝ 3 (@Ring.inverse R _) x‖ ≤ 6*‖Ring.inverse x‖^4 := by
  have h₁ : ‖fderiv ℝ (@Ring.inverse R _) x‖ ≤ ‖Ring.inverse x‖^2 := by
    rw [fderiv_inverse_eq hx, norm_neg, pow_two]
    exact ContinuousLinearMap.opNorm_mulLeftRight_apply_apply_le ℝ R _ _
  have h₂ := inverse_succ_bound hx 1
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,one_mul,zero_add] at h₂
  change ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ ≤
    ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ +
    ‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ at h₂
  simp only [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one] at h₂
  have h₂' : ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ ≤ 2*‖Ring.inverse x‖^3 := by
    calc
      _ ≤ ‖Ring.inverse x‖ * ‖fderiv ℝ (@Ring.inverse R _) x‖ +
          ‖fderiv ℝ (@Ring.inverse R _) x‖ * ‖Ring.inverse x‖ := h₂
      _ ≤ ‖Ring.inverse x‖ * ‖Ring.inverse x‖^2 + ‖Ring.inverse x‖^2 * ‖Ring.inverse x‖ := by gcongr
      _ = _ := by ring
  have h₃ := inverse_succ_bound hx 2
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add] at h₃
  change ‖iteratedFDeriv ℝ 3 (@Ring.inverse R _) x‖ ≤
    ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ +
    2*‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 1 (@Ring.inverse R _) x‖ +
    ‖iteratedFDeriv ℝ 2 (@Ring.inverse R _) x‖ * ‖iteratedFDeriv ℝ 0 (@Ring.inverse R _) x‖ at h₃
  simp only [norm_iteratedFDeriv_zero,norm_iteratedFDeriv_one] at h₃
  refine ⟨h₁,h₂',h₃.trans ?_⟩
  calc
    _ ≤ ‖Ring.inverse x‖*(2*‖Ring.inverse x‖^3) +
        2*‖Ring.inverse x‖^2*‖Ring.inverse x‖^2 +
        (2*‖Ring.inverse x‖^3)*‖Ring.inverse x‖ := by gcongr
    _ = _ := by ring

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_IteratedNormCompLinear
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Calculus

section
open Set
open scoped Topology

variable {E F G D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

lemma iterated_norm_comp_linear (L : E →L[ℝ] F) {f : F → G} {x : E} {n : ℕ}
    (hf : ContDiffAt ℝ n f (L x)) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖*‖L‖^n := by
  obtain ⟨u,hu,hxu,hfu⟩ := hf.contDiffOn' le_rfl (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
  have hfu : ContDiffOn ℝ n f u := by simpa using hfu
  have hpre : IsOpen (L ⁻¹' u) := hu.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hfu hu.uniqueDiffOn hpre.uniqueDiffOn hxu (le_refl (n : WithTop ℕ∞))
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hpre.uniqueDiffOn (hf.comp x L.contDiff.contDiffAt) hxu,
    iteratedFDerivWithin_eq_iteratedFDeriv hu.uniqueDiffOn hf hxu] at he
  rw [he]
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] using
    (iteratedFDeriv ℝ n f (L x)).norm_compContinuousLinearMap_le (fun _ => L)

lemma iterated_norm_comp_contraction (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1)
    {f : F → G} {x : E} {n : ℕ} (hf : ContDiffAt ℝ n f (L x)) :
    ‖iteratedFDeriv ℝ n (f ∘ L) x‖ ≤ ‖iteratedFDeriv ℝ n f (L x)‖ := by
  apply (iterated_norm_comp_linear L hf).trans
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hL)

lemma iterated_norm_linear_ge_two (L : E →L[ℝ] F) (x : E) (n : ℕ) :
    ‖iteratedFDeriv ℝ (n+2) L x‖=0 := by
  rw [show n+2=(n+1)+1 by omega, ← norm_iteratedFDeriv_fderiv]
  have he : fderiv ℝ L = fun _ => L := by funext y; exact L.fderiv
  rw [he,iteratedFDeriv_succ_const]
  simp

lemma bilinear_one (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} (hf : ContDiffAt ℝ 1 f x) (hg : ContDiffAt ℝ 1 g x) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 1 f x‖*‖g x‖ := by
  have h := bilinear_iterated_bound B hf hg hB
  simp only [Finset.sum_range_succ,Finset.sum_range_one,Nat.choose_zero_right,
    Nat.choose_self,Nat.cast_one,one_mul] at h
  change ‖iteratedFDeriv ℝ 1 (fun y => B (f y) (g y)) x‖ ≤
    ‖iteratedFDeriv ℝ 0 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
    ‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at h
  simpa only [norm_iteratedFDeriv_zero] using h

lemma bilinear_two (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 2 (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
      ‖iteratedFDeriv ℝ 2 f x‖*‖g x‖ := by
  have h := bilinear_iterated_bound B hf hg hB
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.choose_zero_right,
    Nat.choose_self,Nat.choose_one_right,Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add] at h
  change ‖iteratedFDeriv ℝ 2 (fun y => B (f y) (g y)) x‖ ≤
    ‖iteratedFDeriv ℝ 0 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
    2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
    ‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at h
  simpa only [norm_iteratedFDeriv_zero] using h

lemma bilinear_three (B : E →L[ℝ] F →L[ℝ] G) {f : D → E} {g : D → F}
    {x : D} (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x) (hB : ‖B‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 3 (fun y => B (f y) (g y)) x‖ ≤
      ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
      3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 3 f x‖*‖g x‖ := by
  have h := bilinear_iterated_bound B hf hg hB
  norm_num only [Finset.sum_range_succ,Finset.sum_range_one,Finset.sum_range_zero,Nat.choose,
    Nat.cast_zero,Nat.cast_one,Nat.cast_ofNat,one_mul,zero_add] at h
  change ‖iteratedFDeriv ℝ 3 (fun y => B (f y) (g y)) x‖ ≤
    ‖iteratedFDeriv ℝ 0 f x‖*‖iteratedFDeriv ℝ 3 g x‖+
    3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
    3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
    ‖iteratedFDeriv ℝ 3 f x‖*‖iteratedFDeriv ℝ 0 g x‖ at h
  simpa only [norm_iteratedFDeriv_zero] using h

end

open Set

variable {E R : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedRing R] [HasSummableGeomSeries R] [NormedAlgebra ℝ R]

lemma iterated_norm_linear_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] (L : F →L[ℝ] G) {f : E → F} {x : E}
    {n : ℕ} (hf : ContDiffAt ℝ n f x) :
    ‖iteratedFDeriv ℝ n (L ∘ f) x‖ ≤ ‖L‖*‖iteratedFDeriv ℝ n f x‖ := by
  rw [L.iteratedFDeriv_comp_left hf le_rfl]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

lemma inverse_linear_first_three (X : E →L[ℝ] R) (hX : ‖X‖ ≤ 1) {z : E}
    (hz : IsUnit (X z)) {a : ℝ} (ha : ‖Ring.inverse (X z)‖ ≤ a) :
    ‖iteratedFDeriv ℝ 1 (fun v => Ring.inverse (X v)) z‖ ≤ a^2 ∧
    ‖iteratedFDeriv ℝ 2 (fun v => Ring.inverse (X v)) z‖ ≤ 2*a^3 ∧
    ‖iteratedFDeriv ℝ 3 (fun v => Ring.inverse (X v)) z‖ ≤ 6*a^4 := by
  have h₀ : 0 ≤ a := (norm_nonneg _).trans ha
  have h := inverse_first_three hz
  have hc (n : ℕ) := iterated_norm_comp_contraction X hX
    (contDiffAt_inverse_of_unit (n := n) hz)
  refine ⟨(hc 1).trans ?_,(hc 2).trans ?_,(hc 3).trans ?_⟩
  · rw [norm_iteratedFDeriv_one]
    exact h.1.trans (pow_le_pow_left₀ (norm_nonneg _) ha _)
  · exact h.2.1.trans (by gcongr)
  · exact h.2.2.trans (by gcongr)

theorem inverse_sandwich_first_three (X P : E →L[ℝ] R)
    (hX : ‖X‖ ≤ 1) (hP : ‖P‖ ≤ 1) {z : E} (hz : IsUnit (X z))
    {a : ℝ} (ha₁ : 1 ≤ a) (ha : ‖Ring.inverse (X z)‖ ≤ a) (hp : ‖P z‖ ≤ 1) :
    ‖iteratedFDeriv ℝ 1 (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) z‖ ≤ 3*a^3 ∧
    ‖iteratedFDeriv ℝ 2 (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) z‖ ≤ 10*a^4 ∧
    ‖iteratedFDeriv ℝ 3 (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) z‖ ≤ 42*a^5 := by
  let f : E → R := fun v => Ring.inverse (X v)
  let g : E → R := fun v => P v*f v
  have hf (n : ℕ) : ContDiffAt ℝ n f z :=
    (contDiffAt_inverse_of_unit hz).comp z X.contDiff.contDiffAt
  have hg (n : ℕ) : ContDiffAt ℝ n g z := P.contDiff.contDiffAt.mul (hf n)
  have hB : ‖ContinuousLinearMap.mul ℝ R‖ ≤ 1 := ContinuousLinearMap.opNorm_mul_le ℝ R
  have h₀ : 0 ≤ a := by linarith
  have ha₂ : a ≤ a^2 := by nlinarith
  have ha₃ : a^2 ≤ a^3 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr ha₂)]
  have ha₄ : a^3 ≤ a^4 := by nlinarith [mul_nonneg h₀ (sub_nonneg.mpr ha₃)]
  obtain ⟨hi₁,hi₂,hi₃⟩ := inverse_linear_first_three X hX hz ha
  have hp₁ : ‖iteratedFDeriv ℝ 1 P z‖ ≤ 1 := by
    simpa only [norm_iteratedFDeriv_one,P.fderiv] using hP
  have hp₂ : ‖iteratedFDeriv ℝ 2 P z‖=0 := iterated_norm_linear_ge_two P z 0
  have hp₃ : ‖iteratedFDeriv ℝ 3 P z‖=0 := iterated_norm_linear_ge_two P z 1
  have hg₀ : ‖g z‖ ≤ a := (norm_mul_le _ _).trans (by simpa using mul_le_mul hp ha (norm_nonneg _) (by norm_num : (0:ℝ)≤1))
  have hg₁ : ‖iteratedFDeriv ℝ 1 g z‖ ≤ 2*a^2 := by
    calc
      _ ≤ ‖P z‖*‖iteratedFDeriv ℝ 1 f z‖+‖iteratedFDeriv ℝ 1 P z‖*‖f z‖ :=
        bilinear_one (ContinuousLinearMap.mul ℝ R) P.contDiff.contDiffAt (hf 1) hB
      _ ≤ 1*a^2+1*a := by gcongr
      _ ≤ _ := by nlinarith
  have hg₂ : ‖iteratedFDeriv ℝ 2 g z‖ ≤ 4*a^3 := by
    have h := bilinear_two (ContinuousLinearMap.mul ℝ R) P.contDiff.contDiffAt (hf 2) hB
    rw [hp₂,zero_mul,add_zero] at h
    calc
      _ ≤ ‖P z‖*‖iteratedFDeriv ℝ 2 f z‖+2*‖iteratedFDeriv ℝ 1 P z‖*‖iteratedFDeriv ℝ 1 f z‖ := h
      _ ≤ 1*(2*a^3)+2*1*a^2 := by gcongr
      _ ≤ _ := by nlinarith
  have hg₃ : ‖iteratedFDeriv ℝ 3 g z‖ ≤ 12*a^4 := by
    have h := bilinear_three (ContinuousLinearMap.mul ℝ R) P.contDiff.contDiffAt (hf 3) hB
    rw [hp₂,hp₃,mul_zero,zero_mul,zero_mul,add_zero,add_zero] at h
    calc
      _ ≤ ‖P z‖*‖iteratedFDeriv ℝ 3 f z‖+3*‖iteratedFDeriv ℝ 1 P z‖*‖iteratedFDeriv ℝ 2 f z‖ := h
      _ ≤ 1*(6*a^4)+3*1*(2*a^3) := by gcongr
      _ ≤ _ := by nlinarith
  have he : (fun v => Ring.inverse (X v)*P v*Ring.inverse (X v)) =
      (fun v => f v*g v) := by funext v; exact mul_assoc _ _ _
  rw [he]
  refine ⟨?_,?_,?_⟩
  · calc
      _ ≤ ‖f z‖*‖iteratedFDeriv ℝ 1 g z‖+‖iteratedFDeriv ℝ 1 f z‖*‖g z‖ :=
        bilinear_one (ContinuousLinearMap.mul ℝ R) (hf 1) (hg 1) hB
      _ ≤ a*(2*a^2)+a^2*a := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ‖f z‖*‖iteratedFDeriv ℝ 2 g z‖+2*‖iteratedFDeriv ℝ 1 f z‖*‖iteratedFDeriv ℝ 1 g z‖+
          ‖iteratedFDeriv ℝ 2 f z‖*‖g z‖ := bilinear_two (ContinuousLinearMap.mul ℝ R) (hf 2) (hg 2) hB
      _ ≤ a*(4*a^3)+2*a^2*(2*a^2)+(2*a^3)*a := by gcongr
      _ = _ := by ring
  · calc
      _ ≤ ‖f z‖*‖iteratedFDeriv ℝ 3 g z‖+3*‖iteratedFDeriv ℝ 1 f z‖*‖iteratedFDeriv ℝ 2 g z‖+
          3*‖iteratedFDeriv ℝ 2 f z‖*‖iteratedFDeriv ℝ 1 g z‖+
          ‖iteratedFDeriv ℝ 3 f z‖*‖g z‖ := bilinear_three (ContinuousLinearMap.mul ℝ R) (hf 3) (hg 3) hB
      _ ≤ a*(12*a^4)+3*a^2*(4*a^3)+3*(2*a^3)*(2*a^2)+(6*a^4)*a := by gcongr
      _ = _ := by ring
end CurrentKS.Calculus

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_JetBound
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
open Set

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

lemma JetBound.nonneg {f : E → F} {x : E} {B : ℝ} (h : JetBound f x B) : 0 ≤ B :=
  (norm_nonneg _).trans (h 0 (by omega))

lemma JetBound.value {f : E → F} {x : E} {B : ℝ} (h : JetBound f x B) : ‖f x‖ ≤ B := by
  simpa only [norm_iteratedFDeriv_zero] using h 0 (by omega)

lemma JetBound.mono {f : E → F} {x : E} {B C : ℝ} (h : JetBound f x B) (hBC : B ≤ C) :
    JetBound f x C := fun n hn => (h n hn).trans hBC

lemma JetBound.add {f g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => f y+g y) x (B+C) := by
  intro n hn
  rw [fun_iteratedFDeriv_add_apply (hf.of_le (by exact_mod_cast hn)) (hg.of_le (by exact_mod_cast hn))]
  exact (norm_add_le _ _).trans (add_le_add (hB n hn) (hC n hn))

lemma JetBound.neg {f : E → F} {x : E} {B : ℝ} (hB : JetBound f x B) :
    JetBound (fun y => -f y) x B := by
  intro n hn
  change ‖iteratedFDeriv ℝ n (-f) x‖ ≤ B
  rw [iteratedFDeriv_neg_apply,norm_neg]
  exact hB n hn

lemma JetBound.sub {f g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => f y-g y) x (B+C) := by
  simpa only [sub_eq_add_neg] using hB.add hf hg.neg hC.neg

lemma JetBound.linear_comp {f : E → F} {x : E} {B C : ℝ} (L : F →L[ℝ] G)
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hL : ‖L‖ ≤ C) :
    JetBound (L ∘ f) x (C*B) := by
  intro n hn
  exact (iterated_norm_linear_comp L (hf.of_le (by exact_mod_cast hn))).trans
    (mul_le_mul hL (hB n hn) (norm_nonneg _) ((norm_nonneg L).trans hL))

lemma JetBound.prod {f : E → F} {g : E → G} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) : JetBound (fun y => (f y,g y)) x (B+C) := by
  intro n hn
  rw [iteratedFDeriv_prodMk hf hg (by exact_mod_cast hn),ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact (hB n hn).trans (le_add_of_nonneg_right hC.nonneg)
  · exact (hC n hn).trans (le_add_of_nonneg_left hB.nonneg)

lemma JetBound.const (v : F) (x : E) : JetBound (fun _ : E => v) x ‖v‖ := by
  intro n _
  cases n with
  | zero => simp only [norm_iteratedFDeriv_zero, le_refl]
  | succ n => simp only [iteratedFDeriv_succ_const,Pi.zero_apply,norm_zero,norm_nonneg]

lemma JetBound.linear (L : E →L[ℝ] F) (x : E) {B : ℝ} (hLB : ‖L‖ ≤ B) (hx : ‖L x‖ ≤ B) :
    JetBound L x B := by
  intro n hn
  interval_cases n
  · simpa only [norm_iteratedFDeriv_zero] using hx
  · simpa only [norm_iteratedFDeriv_one,L.fderiv] using hLB
  · rw [iterated_norm_linear_ge_two L x 0]
    exact (norm_nonneg L).trans hLB
  · rw [iterated_norm_linear_ge_two L x 1]
    exact (norm_nonneg L).trans hLB

lemma JetBound.bilinear (L : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    {x : E} {B C : ℝ} (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) (hL : ‖L‖ ≤ 1) :
    JetBound (fun y => L (f y) (g y)) x (8*B*C) := by
  have hB0 := hB.value
  have hC0 := hC.value
  have hB1 := hB 1 (by omega)
  have hC1 := hC 1 (by omega)
  have hB2 := hB 2 (by omega)
  have hC2 := hC 2 (by omega)
  have hB3 := hB 3 (by omega)
  have hC3 := hC 3 (by omega)
  have hBn := hB.nonneg
  have hCn := hC.nonneg
  have hBC := mul_nonneg hBn hCn
  intro n hn
  interval_cases n
  · rw [norm_iteratedFDeriv_zero]
    calc
      _ ≤ ‖L‖*‖f x‖*‖g x‖ := L.le_opNorm₂ _ _
      _ ≤ 1*B*C := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 1 f x‖*‖g x‖ :=
        bilinear_one L (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hL
      _ ≤ B*C+B*C := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖f x‖*‖iteratedFDeriv ℝ 2 g x‖+2*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 1 g x‖+
          ‖iteratedFDeriv ℝ 2 f x‖*‖g x‖ := bilinear_two L (hf.of_le (by norm_num)) (hg.of_le (by norm_num)) hL
      _ ≤ B*C+2*B*C+B*C := by gcongr
      _ ≤ _ := by nlinarith
  · calc
      _ ≤ ‖f x‖*‖iteratedFDeriv ℝ 3 g x‖+3*‖iteratedFDeriv ℝ 1 f x‖*‖iteratedFDeriv ℝ 2 g x‖+
          3*‖iteratedFDeriv ℝ 2 f x‖*‖iteratedFDeriv ℝ 1 g x‖+‖iteratedFDeriv ℝ 3 f x‖*‖g x‖ :=
        bilinear_three L hf hg hL
      _ ≤ B*C+3*B*C+3*B*C+B*C := by gcongr
      _ = _ := by ring
end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Calculus_NormSmulRightId
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Calculus
noncomputable section
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma norm_smulRight_id_le (v : F) :
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v)
  intro r
  change ‖r • v‖ ≤ ‖v‖*‖r‖
  rw [norm_smul,mul_comm]

lemma JetBound.smul_const {f : E → ℝ} {x : E} {B C : ℝ} (v : F)
    (hf : ContDiffAt ℝ 3 f x) (hB : JetBound f x B) (hC : ‖v‖ ≤ C) :
    JetBound (fun y => f y • v) x (C*B) := by
  exact hB.linear_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight v) hf
    ((norm_smulRight_id_le v).trans hC)

attribute [local instance] OAI.CurrentKS.Calculus.instNormedAddCommGroupContinuousLinearMapRealId_solutions
attribute [local instance] OAI.CurrentKS.Calculus.instNormedSpaceRealContinuousLinearMapId_solutions
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_1_rea7e91_1 : NormedAddCommGroup ((G →L[ℝ] F) →L[ℝ] F) := inferInstance
attribute [local instance] OAI.CurrentKS.Calculus.instNormedSpaceRealContinuousLinearMapId_solutions_1
attribute [local instance] OAI.CurrentKS.Calculus.instNormedAddCommGroupContinuousLinearMapRealId_solutions_2
attribute [local instance] OAI.CurrentKS.Calculus.instNormedSpaceRealContinuousLinearMapId_solutions_2
local instance instNormedAddCommGroupContinuousLinearMapRealId_solutions_3_rea7e91_1 : NormedAddCommGroup ((F →L[ℝ] G) →L[ℝ] G) := inferInstance
attribute [local instance] OAI.CurrentKS.Calculus.instNormedSpaceRealContinuousLinearMapId_solutions_3
lemma norm_apply_bilinear_le : ‖ContinuousLinearMap.apply ℝ F (E := G)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro L
  change ‖L v‖ ≤ (1*‖v‖)*‖L‖
  simpa only [one_mul,mul_one,mul_comm] using L.le_opNorm v

lemma JetBound.apply {f : E → F →L[ℝ] G} {g : E → F} {x : E} {B C : ℝ}
    (hf : ContDiffAt ℝ 3 f x) (hg : ContDiffAt ℝ 3 g x)
    (hB : JetBound f x B) (hC : JetBound g x C) :
    JetBound (fun y => f y (g y)) x (8*C*B) := by
  exact JetBound.bilinear (E := E) (F := F) (G := F →L[ℝ] G) (H := G)
    (ContinuousLinearMap.apply ℝ G (E := F)) hg hf hC hB
    (norm_apply_bilinear_le (F := G) (G := F))

lemma norm_comp_contractions (L : F →L[ℝ] G) (T : E →L[ℝ] F)
    (hL : ‖L‖ ≤ 1) (hT : ‖T‖ ≤ 1) : ‖L.comp T‖ ≤ 1 :=
  (ContinuousLinearMap.opNorm_comp_le L T).trans
    (by simpa only [one_mul] using mul_le_mul hL hT (norm_nonneg T) zero_le_one)

end
end CurrentKS.Calculus

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_HermitianMat
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.invH_val _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.realTrace_add _root_.OAI.CurrentKS.Hermitian.realTrace_one _root_.OAI.CurrentKS.Hermitian.realTrace_smul _root_.OAI.CurrentKS.Hermitian.realTrace_sub _root_.OAI.CurrentKS.Hermitian.realTrace_zero _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix
open scoped BigOperators ComplexOrder InnerProductSpace

variable {d : ℕ}

open scoped Matrix.Norms.Frobenius

theorem matrix_inner (d : ℕ) (A B : Mat d) :
    inner ℂ A B = (B * Aᴴ).trace := by
  change inner ℂ (asL2 A) (asL2 B) = _
  simp only [asL2, PiLp.inner_apply, RCLike.inner_apply,
    Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply]
  congr 1

theorem inner_eq_trace (A B : H d) :
    inner ℝ A B = ((A : Mat d) * (B : Mat d)).trace.re := by
  change (inner ℂ (A : Mat d) (B : Mat d)).re = _
  rw [matrix_inner, A.property.eq, Matrix.trace_mul_comm]

@[simp] theorem inner_one (A : H d) : inner ℝ one A = realTrace A := by
  rw [inner_eq_trace, one_val, one_mul]
  rfl

@[simp] theorem inner_one' (A : H d) : inner ℝ A one = realTrace A := by
  rw [real_inner_comm]
  exact inner_one A

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_TraceCLM
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Hermitian.matrixTraceCLM_apply _root_.OAI.CurrentKS.Hermitian.retractH_coe _root_.OAI.CurrentKS.Hermitian.sandwichCLM_apply _root_.OAI.CurrentKS.Hermitian.sandwich_val _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

@[simp] lemma traceCLM_apply (A : H d) : traceCLM A = realTrace A := inner_one A

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_RetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Hermitian
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p6
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p6
lemma invH_retract (A : H d) : invH A = retractH (Ring.inverse (A : Mat d)) := by
  rw [← Matrix.nonsing_inv_eq_ringInverse]
  exact (retractH_coe (invH A)).symm

lemma contDiffAt_invH {A : H d} (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n invH A := by
  obtain ⟨a,ha⟩ := hA.isUnit
  have hi : ContDiffAt ℝ n Ring.inverse (A : Mat d) := by
    rw [← ha]
    exact contDiffAt_ringInverse ℝ a
  have hc := (retractH (d := d)).contDiff.contDiffAt.comp A
    (hi.comp A (hermitianSubmodule d).subtypeL.contDiff.contDiffAt)
  apply hc.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun B => invH_retract B

lemma contDiff_sandwich {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun z : H d × H d => sandwich z.1 z.2) := by
  have hf : (fun z : H d × H d => sandwich z.1 z.2) =
      (fun z : H d × H d => retractH ((z.1 : Mat d) * (z.2 : Mat d) * (z.1 : Mat d))) := by
    funext z
    exact (retractH_coe (sandwich z.1 z.2)).symm
  rw [hf]
  apply (retractH (d := d)).contDiff.comp
  exact (((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst).mul
    ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_snd)).mul
      ((hermitianSubmodule d).subtypeL.contDiff.comp contDiff_fst)

lemma contDiffAt_invSandwich (A P : H d) (hA : A ∈ pd d) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun z : H d × H d => sandwich (invH z.1) z.2) (A,P) := by
  have hi : ContDiffAt ℝ n (fun z : H d × H d => invH z.1) (A,P) :=
    (contDiffAt_invH (d := d) (A := A) (n := n) hA).fst' (y := P)
  have hp : ContDiffAt ℝ n (fun z : H d × H d => (invH z.1, z.2)) (A,P) :=
    hi.prodMk (contDiffAt_snd (𝕜 := ℝ) (n := n) (p := (A,P)))
  have hs : ContDiffAt ℝ n (fun u : H d × H d => sandwich u.1 u.2) (invH A,P) :=
    (contDiff_sandwich (d := d) (n := n)).contDiffAt
  exact hs.comp (A,P) hp

end CurrentKS.Hermitian

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_FDerivTightPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius ContDiff

variable {d : ℕ}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
lemma contDiffAt_tightPart {n : WithTop ℕ∞} {t : E → ℝ} {X Y S : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E}
    (ht : ContDiffAt ℝ n t z) (hX : ContDiffAt ℝ n X z) (hY : ContDiffAt ℝ n Y z)
    (hS : ContDiffAt ℝ n S z) (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z :=
  (((ht.smul contDiffAt_const).sub ((contDiffAt_invH hpos).comp z hX)).sub hS).sub
    (hη.clm_apply hY)

lemma contDiffAt_stationaryPart {n : WithTop ℕ∞} {X P Q : E → H d}
    {η : E → (H d →L[ℝ] H d)} {z : E} (ε : ℝ)
    (hX : ContDiffAt ℝ n X z) (hP : ContDiffAt ℝ n P z) (hQ : ContDiffAt ℝ n Q z)
    (hη : ContDiffAt ℝ n η z) (hpos : X z ∈ pd d) :
    ContDiffAt ℝ n (fun v => sandwich (invH (X v)) (P v) - η v (Q v) - ε • (one : H d)) z :=
  (((contDiffAt_invSandwich (X z) (P z) hpos).comp z (hX.prodMk hP)).sub
    (hη.clm_apply hQ)).sub contDiffAt_const

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_NormRetractH
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p5
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p5
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p1
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p5
lemma norm_retractH_le : ‖(retractH (d := d) : Mat d →L[ℝ] H d)‖ ≤ 1 :=
  (hermitianSubmodule d).orthogonalProjectionOnto_norm_le

lemma norm_subtypeH_le : ‖(hermitianSubmodule d).subtypeL‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖v‖ ≤ 1 * ‖v‖
  simp only [one_mul, le_refl]

lemma jetBound_invH_linear (X : E →L[ℝ] H d) (hX : ‖X‖ ≤ 1) {z : E}
    (hz : X z ∈ pd d) {a : ℝ} (ha₁ : 1 ≤ a) (ha : ‖invH (X z)‖ ≤ a) :
    JetBound (fun v => invH (X v)) z (6*a^4) := by
  let Xm := (hermitianSubmodule d).subtypeL.comp X
  have hXm : ‖Xm‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul norm_subtypeH_le hX (norm_nonneg X) zero_le_one)
  have ham : ‖Ring.inverse (Xm z)‖ ≤ a := by
    simp only [Xm,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      ← Matrix.nonsing_inv_eq_ringInverse]
    exact ha
  have hzunit : IsUnit (Xm z) := hz.isUnit
  obtain ⟨h₁,h₂,h₃⟩ := inverse_linear_first_three Xm hXm hzunit ham
  have hc : ContDiffAt ℝ 3 (fun v => Ring.inverse (Xm v)) z :=
    (contDiffAt_inverse_of_unit hzunit).comp z Xm.contDiff.contDiffAt
  have hm : JetBound (fun v => Ring.inverse (Xm v)) z (6*a^4) := by
    have ha0 : 0 ≤ a := le_trans zero_le_one ha₁
    have ha14 : a ≤ a^4 := by simpa only [pow_one] using pow_le_pow_right₀ ha₁ (by norm_num : 1≤4)
    have ha24 : a^2 ≤ a^4 := pow_le_pow_right₀ ha₁ (by norm_num)
    have ha34 : a^3 ≤ a^4 := pow_le_pow_right₀ ha₁ (by norm_num)
    intro n hn
    interval_cases n
    · rw [norm_iteratedFDeriv_zero]; exact ham.trans (by nlinarith [pow_nonneg ha0 4])
    · exact h₁.trans (by nlinarith [pow_nonneg ha0 4])
    · exact h₂.trans (by nlinarith [pow_nonneg ha0 4])
    · exact h₃
  have h := hm.linear_comp (retractH (d := d)) hc norm_retractH_le
  simpa only [Function.comp_def,one_mul,Xm,ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply,← invH_retract] using h

end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JetBoundInverseSandwich
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
attribute [-simp] _root_.OAI.CurrentKS.Variational.linCongruence_apply _root_.OAI.CurrentKS.Variational.linConstraint_apply _root_.OAI.CurrentKS.Variational.linPositive_apply _root_.OAI.CurrentKS.Variational.mem_pairCone
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]


attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupMat_p0
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealMat_p0
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceMat_p0
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p2
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p2
lemma jetBound_inverse_sandwich (X P : E →L[ℝ] H d)
    (hX : ‖X‖ ≤ 1) (hP : ‖P‖ ≤ 1) {z : E} (hz : X z ∈ pd d)
    {a : ℝ} (ha₁ : 1 ≤ a) (ha : ‖invH (X z)‖ ≤ a) (hp : ‖P z‖ ≤ 1) :
    JetBound (fun v => sandwich (invH (X v)) (P v)) z (42*a^5) := by
  let Xm := (hermitianSubmodule d).subtypeL.comp X
  let Pm := (hermitianSubmodule d).subtypeL.comp P
  have hXm : ‖Xm‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul norm_subtypeH_le hX (norm_nonneg X) zero_le_one)
  have hPm : ‖Pm‖ ≤ 1 := (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul norm_subtypeH_le hP (norm_nonneg P) zero_le_one)
  have ham : ‖Ring.inverse (Xm z)‖ ≤ a := by
    simp only [Xm,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      ← Matrix.nonsing_inv_eq_ringInverse]
    exact ha
  have hpm : ‖Pm z‖ ≤ 1 := hp
  have hzunit : IsUnit (Xm z) := hz.isUnit
  have h₀ : 0 ≤ a := le_trans zero_le_one ha₁
  obtain ⟨h₁,h₂,h₃⟩ := inverse_sandwich_first_three Xm Pm hXm hPm hzunit ha₁ ham hp
  have hi : ContDiffAt ℝ 3 (fun v => Ring.inverse (Xm v)) z :=
    (contDiffAt_inverse_of_unit hzunit).comp z Xm.contDiff.contDiffAt
  let f := fun v => Ring.inverse (Xm v)*Pm v*Ring.inverse (Xm v)
  have hf : ContDiffAt ℝ 3 f z := (hi.mul Pm.contDiff.contDiffAt).mul hi
  have hb : JetBound f z (42*a^5) := by
    have ha25 : a^2 ≤ a^5 := pow_le_pow_right₀ ha₁ (by norm_num)
    have ha35 : a^3 ≤ a^5 := pow_le_pow_right₀ ha₁ (by norm_num)
    have ha45 : a^4 ≤ a^5 := pow_le_pow_right₀ ha₁ (by norm_num)
    have hv : ‖f z‖ ≤ a^2 := by
      calc
        _ ≤ ‖Ring.inverse (Xm z)‖*‖Pm z‖*‖Ring.inverse (Xm z)‖ :=
          (norm_mul_le _ _).trans
            (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
        _ ≤ a*1*a := mul_le_mul (mul_le_mul ham hpm (norm_nonneg _) h₀) ham (norm_nonneg _) (by positivity)
        _ = _ := by ring
    intro n hn
    interval_cases n
    · rw [norm_iteratedFDeriv_zero]; exact hv.trans (by nlinarith [pow_nonneg h₀ 5])
    · exact h₁.trans (by nlinarith [pow_nonneg h₀ 5])
    · exact h₂.trans (by nlinarith [pow_nonneg h₀ 5])
    · exact h₃
  have hh := hb.linear_comp (retractH (d := d)) hf norm_retractH_le
  have he : (retractH (d := d)) ∘ f = fun v => sandwich (invH (X v)) (P v) := by
    funext v
    change retractH (Ring.inverse (Xm v)*Pm v*Ring.inverse (Xm v)) = _
    simp only [Xm,Pm,ContinuousLinearMap.comp_apply,Submodule.subtypeL_apply,
      ← Matrix.nonsing_inv_eq_ringInverse]
    exact retractH_coe (sandwich (invH (X v)) (P v))
  rw [he,one_mul] at hh
  exact hh
end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Matrices_JetBoundTightPart
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Hermitian
noncomputable section
open CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealSubtypeMatMemSubmoduleH_p3
attribute [local instance] OAI.CurrentKS.Hermitian.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p3
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Hermitian.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1_rea7e91_1 : NormedAddCommGroup (E →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_1_rea7e91_1 : NormedSpace ℝ (E →L[ℝ] H d) := inferInstance
lemma jetBound_tightPart (t : E →L[ℝ] ℝ) (X Y : E →L[ℝ] H d)
    {S : E → H d} {η : E → H d →L[ℝ] H d} {z : E} {B : ℝ}
    (hB : 1 ≤ B) (hI : ‖(one : H d)‖ ≤ B)
    (ht : JetBound t z B) (hX : ‖X‖ ≤ 1) (hY : JetBound Y z B)
    (hpos : X z ∈ pd d) (hinv : ‖invH (X z)‖ ≤ B)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => t v • (one : H d) - invH (X v) - S v - η v (Y v)) z
      (B*B+6*B^4+B+8*B*B) := by
  have h₁ := ht.smul_const (one : H d) t.contDiff.contDiffAt hI
  have h₂ := jetBound_invH_linear X hX hpos hB hinv
  have h₃ := hηB.apply hη Y.contDiff.contDiffAt hY
  have hc₁ : ContDiffAt ℝ 3 (fun v => t v • (one : H d)) z :=
    t.contDiff.contDiffAt.smul contDiffAt_const
  have hc₂ : ContDiffAt ℝ 3 (fun v => invH (X v)) z :=
    (contDiffAt_invH hpos).comp z X.contDiff.contDiffAt
  exact ((h₁.sub hc₁ hc₂ h₂).sub (hc₁.sub hc₂) hS hSB).sub
    ((hc₁.sub hc₂).sub hS) (hη.clm_apply Y.contDiff.contDiffAt) h₃

lemma jetBound_stationaryPart (X P Q : E →L[ℝ] H d) (ε : ℝ)
    {η : E → H d →L[ℝ] H d} {z : E} {B : ℝ}
    (hB : 1 ≤ B) (hI : ‖(one : H d)‖ ≤ B) (hε : |ε| ≤ B)
    (hX : ‖X‖ ≤ 1) (hP : ‖P‖ ≤ 1) (hPB : ‖P z‖ ≤ 1)
    (hQ : JetBound Q z B) (hpos : X z ∈ pd d) (hinv : ‖invH (X z)‖ ≤ B)
    (hη : ContDiffAt ℝ 3 η z) (hηB : JetBound η z B) :
    JetBound (fun v => sandwich (invH (X v)) (P v) - η v (Q v) - ε • (one : H d)) z
      (42*B^5+8*B*B+B*B) := by
  have h₁ := jetBound_inverse_sandwich X P hX hP hpos hB hinv hPB
  have h₂ := hηB.apply hη Q.contDiff.contDiffAt hQ
  have h₃ := (JetBound.const (ε • (one : H d)) z).mono
    (show ‖ε • (one : H d)‖ ≤ B*B by
      rw [norm_smul,Real.norm_eq_abs]
      exact mul_le_mul hε hI (norm_nonneg _) (le_trans zero_le_one hB))
  have hc₁ : ContDiffAt ℝ 3 (fun v => sandwich (invH (X v)) (P v)) z :=
    (contDiffAt_invSandwich _ _ hpos).comp z (X.contDiff.contDiffAt.prodMk P.contDiff.contDiffAt)
  exact (h₁.sub hc₁ (hη.clm_apply Q.contDiff.contDiffAt) h₂).sub
    (hc₁.sub (hη.clm_apply Q.contDiff.contDiffAt)) contDiffAt_const h₃
end
end CurrentKS.Hermitian

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormSq
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1_p1
lemma norm_one_sq : ‖(Hermitian.one : H d)‖^2 = (d : ℝ) := by
  rw [← real_inner_self_eq_norm_sq,inner_one,realTrace_one]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p1
lemma identityPair_norm_sq : ‖identityPair d‖^2 = 2*(d : ℝ) := by
  rw [WithLp.prod_norm_sq_eq_of_L2]
  change ‖(Hermitian.one : H d)‖^2+‖(Hermitian.one : H d)‖^2 = _
  rw [norm_one_sq]
  ring

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_NormTCoord
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ}

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p1
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPair
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPair
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePair
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpacePairHilbert_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1_p2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1_p2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p3
lemma norm_tCoord_le : norm (E := Vars d →L[ℝ] ℝ) (tCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact norm_fst_le z
lemma norm_pCoord_le : norm (E := Vars d →L[ℝ] PairHilbert d) (pCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (norm_snd_le z.2).trans (norm_snd_le z)
lemma norm_xCoord_le : norm (E := Vars d →L[ℝ] H d) (xCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_fst_le (H d) z.2.1).trans
    ((norm_fst_le z.2).trans (norm_snd_le z))
lemma norm_yCoord_le : norm (E := Vars d →L[ℝ] H d) (yCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_snd_le (H d) z.2.1).trans
    ((norm_fst_le z.2).trans (norm_snd_le z))
lemma norm_mCoord_le : norm (E := Vars d →L[ℝ] H d) (mCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_fst_le (H d) z.2.2).trans
    ((norm_snd_le z.2).trans (norm_snd_le z))
lemma norm_nCoord_le : norm (E := Vars d →L[ℝ] H d) (nCoord d) ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  simp only [one_mul]
  exact (WithLp.norm_snd_le (H d) z.2.2).trans
    ((norm_snd_le z.2).trans (norm_snd_le z))

lemma norm_pairEquiv_symm_le : norm (E := Pair d →L[ℝ] PairHilbert d) (pairEquiv d).symm.toContinuousLinearMap ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  have he : ‖(pairEquiv d).symm z‖^2 = ‖z.1‖^2+‖z.2‖^2 := WithLp.prod_norm_sq_eq_of_L2 _
  have h₁ := pow_le_pow_left₀ (norm_nonneg z.1) (norm_fst_le z) 2
  have h₂ := pow_le_pow_left₀ (norm_nonneg z.2) (norm_snd_le z) 2
  change ‖(pairEquiv d).symm z‖ ≤ 2*‖z‖
  nlinarith [norm_nonneg ((pairEquiv d).symm z),norm_nonneg z]

lemma norm_one_le_dimension : ‖(Hermitian.one : H d)‖ ≤ (d:ℝ)+1 := by
  have hn := norm_one_sq (d := d)
  have hd := Nat.cast_nonneg (α := ℝ) d
  nlinarith [norm_nonneg (Hermitian.one : H d)]

lemma norm_identityPair_le_dimension : ‖identityPair d‖ ≤ 2*((d:ℝ)+1) := by
  have hn := identityPair_norm_sq (d := d)
  have hd := Nat.cast_nonneg (α := ℝ) d
  nlinarith [norm_nonneg (identityPair d)]

end
end CurrentKS.Variational

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_Parameters
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix

namespace CurrentKS.Variational
open CurrentKS.Hermitian Matrix Set
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius Topology ContDiff

variable {d : ℕ}

section

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p4
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p4
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupParameters
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealParameters
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdParametersVars
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdParametersVars
lemma contDiffAt_kktGiven {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {S : E → H d} {η : E → (H d →L[ℝ] H d)}
    {v : E → Vars d} {b : E} (ε : ℝ)
    (hS : ContDiffAt ℝ n S b) (hη : ContDiffAt ℝ n η b) (hv : ContDiffAt ℝ n v b)
    (hX : xCoord d (v b) ∈ pd d) (hY : yCoord d (v b) ∈ pd d) :
    ContDiffAt ℝ n (fun a => kktSystem ε (S a) (η a) (v a)) b := by
  have ht := (tCoord d).contDiff.contDiffAt.comp b hv
  have hx := (xCoord d).contDiff.contDiffAt.comp b hv
  have hy := (yCoord d).contDiff.contDiffAt.comp b hv
  have hm := (mCoord d).contDiff.contDiffAt.comp b hv
  have hn := (nCoord d).contDiff.contDiffAt.comp b hv
  have hr := (((innerSL ℝ (identityPair d)).contDiff.contDiffAt.comp b
      ((pCoord d).contDiff.contDiffAt.comp b hv)).sub (contDiffAt_const (c := (1 : ℝ))))
  have hfx := contDiffAt_tightPart ht hx hy hS hη hX
  have hfy := contDiffAt_tightPart ht hy hx hS.neg hη hY
  have hfu := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hfx.prodMk hfy)
  have hgx := contDiffAt_stationaryPart ε hx hm hn hη hX
  have hgy := contDiffAt_stationaryPart ε hy hn hm hη hY
  have hgp := (pairEquiv d).symm.contDiff.contDiffAt.comp b (hgx.prodMk hgy)
  have hh := hr.prodMk (hfu.prodMk hgp)
  simp only [sub_neg_eq_add] at hh
  exact hh

end

end CurrentKS.Variational

end

end OAI
end

section
-- module Solutions.OAIQ241_TT.MatrixSigning_Potential_JetBoundProjection
attribute [-instance] _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFinite _root_.OAI.AlgorithmicThinTrees.Partitions.partitionsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Matrix

namespace CurrentKS.Variational
noncomputable section
open CurrentKS.Hermitian CurrentKS.Calculus Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.Frobenius

variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealSubtypeMatMemSubmoduleH_p0
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceSubtypeMatMemSubmoduleRealH_p0
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_1
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdSubtypeMatMemSubmoduleRealH
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdSubtypeMatMemSubmoduleH
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealProdPairHilbert
attribute [local instance] OAI.CurrentKS.Variational.instNormedAddCommGroupVars_2
attribute [local instance] OAI.CurrentKS.Variational.instNormedSpaceRealVars_2
attribute [local instance] OAI.CurrentKS.Variational.instTopologicalSpaceVars_p0
local instance instNormedAddCommGroupContinuousLinearMapRealIdVars_rea7e91_1 : NormedAddCommGroup (E →L[ℝ] Vars d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdVars_rea7e91_1 : NormedSpace ℝ (E →L[ℝ] Vars d) := inferInstance
local instance instNormedAddCommGroupContinuousLinearMapRealIdSubtypeMatMemSubmoduleH_2_rea7e91_1 : NormedAddCommGroup (E →L[ℝ] H d) := inferInstance
local instance instNormedSpaceRealContinuousLinearMapIdSubtypeMatMemSubmoduleH_2_rea7e91_1 : NormedSpace ℝ (E →L[ℝ] H d) := inferInstance
lemma jetBound_projection {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (Z : E →L[ℝ] Vars d) (L : Vars d →L[ℝ] F) {z : E} {B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hL : ‖L‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) :
    JetBound (L.comp Z) z B := by
  apply JetBound.linear _ _ (le_trans (norm_comp_contractions L Z hL hZ) hB)
  exact (L.le_opNorm (Z z)).trans ((mul_le_mul_of_nonneg_right hL (norm_nonneg _)).trans
    (by simpa only [one_mul] using hz))

lemma norm_tracePair_le {B : ℝ} (hd : (d:ℝ)+1 ≤ B) :
    ‖innerSL ℝ (identityPair d)‖ ≤ 2*B := by
  have hB : 0 ≤ B := le_trans (by positivity) hd
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  exact (norm_inner_le_norm (𝕜 := ℝ) (identityPair d) v).trans
    (mul_le_mul_of_nonneg_right ((norm_identityPair_le_dimension (d := d)).trans (show 2*((d:ℝ)+1) ≤ 2*B by linarith)) (norm_nonneg v))

lemma jetBound_pairHilbert {f g : E → H d} {z : E} {C D : ℝ}
    (hf : ContDiffAt ℝ 3 f z) (hg : ContDiffAt ℝ 3 g z)
    (hfB : JetBound f z C) (hgB : JetBound g z D) :
    JetBound (fun v => (pairEquiv d).symm (f v,g v)) z (2*(C+D)) :=
  (hfB.prod hf hg hgB).linear_comp (pairEquiv d).symm.toContinuousLinearMap
    (hf.prodMk hg) norm_pairEquiv_symm_le

lemma jetBound_tracePart (Z : E →L[ℝ] Vars d) {z : E} {B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) :
    JetBound (fun v => inner ℝ (identityPair d) (pCoord d (Z v))-1) z (2*B*B+1) := by
  let p : E →L[ℝ] PairHilbert d := (pCoord d).comp Z
  have hpB := jetBound_projection Z (pCoord d) hZ norm_pCoord_le hz hB
  have htrace := hpB.linear_comp (innerSL ℝ (identityPair d)) p.contDiff.contDiffAt (norm_tracePair_le hd)
  have hh := htrace.sub
    ((innerSL ℝ (identityPair d)).contDiff.contDiffAt.comp z p.contDiff.contDiffAt)
    (contDiffAt_const (c := (1:ℝ))) (JetBound.const (1:ℝ) z)
  simp only [Function.comp_def,norm_one] at hh
  exact hh

lemma kktJet_numeric {B : ℝ} (hB : 1 ≤ B) :
    2*B*B+1+(2*((B*B+6*B^4+B+8*B*B)+(B*B+6*B^4+B+8*B*B))+
      2*((42*B^5+8*B*B+B*B)+(42*B^5+8*B*B+B*B))) ≤ 300*B^5 := by
  have h15 : B ≤ B^5 := by simpa only [pow_one] using pow_le_pow_right₀ hB (by norm_num : 1≤5)
  have h25 : B^2 ≤ B^5 := pow_le_pow_right₀ hB (by norm_num)
  have h45 : B^4 ≤ B^5 := pow_le_pow_right₀ hB (by norm_num)
  have h05 : 1 ≤ B^5 := one_le_pow₀ hB
  nlinarith

lemma jetBound_kktPrimal (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (_hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (_hM : ‖mCoord d (Z z)‖ ≤ 1) (_hN : ‖nCoord d (Z z)‖ ≤ 1)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => (kktSystem ε (S v) (η v) (Z v)).2.1) z
      (2*((B*B+6*B^4+B+8*B*B)+(B*B+6*B^4+B+8*B*B))) := by

  let t : E →L[ℝ] ℝ := (tCoord d).comp Z
  let X : E →L[ℝ] H d := (xCoord d).comp Z
  let Y : E →L[ℝ] H d := (yCoord d).comp Z
  have ht := jetBound_projection Z (tCoord d) hZ norm_tCoord_le hz hB
  have hXB := jetBound_projection Z (xCoord d) hZ norm_xCoord_le hz hB
  have hYB := jetBound_projection Z (yCoord d) hZ norm_yCoord_le hz hB
  have hXL : ‖X‖ ≤ 1 := norm_comp_contractions _ _ norm_xCoord_le hZ
  have hYL : ‖Y‖ ≤ 1 := norm_comp_contractions _ _ norm_yCoord_le hZ
  have hI := (norm_one_le_dimension (d := d)).trans hd
  let T := B*B+6*B^4+B+8*B*B
  have h₁ : JetBound (fun v => t v • (Hermitian.one : H d)-invH (X v)-S v-η v (Y v)) z T :=
    jetBound_tightPart t X Y hB hI ht hXL hYB hX hiX hS hη hSB hηB
  have h₂ : JetBound (fun v => t v • (Hermitian.one : H d)-invH (Y v)-(-S v)-η v (X v)) z T :=
    jetBound_tightPart t Y X hB hI ht hYL hXB hY hiY hS.neg hη hSB.neg hηB
  have hc₁ := contDiffAt_tightPart t.contDiff.contDiffAt X.contDiff.contDiffAt Y.contDiff.contDiffAt hS hη hX
  have hc₂ := contDiffAt_tightPart t.contDiff.contDiffAt Y.contDiff.contDiffAt X.contDiff.contDiffAt hS.neg hη hY
  have h := jetBound_pairHilbert hc₁ hc₂ h₁ h₂
  simp only [sub_neg_eq_add] at h
  exact h

lemma jetBound_kktDual (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (hM : ‖mCoord d (Z z)‖ ≤ 1) (hN : ‖nCoord d (Z z)‖ ≤ 1)
    (_hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (_hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => (kktSystem ε (S v) (η v) (Z v)).2.2) z
      (2*((42*B^5+8*B*B+B*B)+(42*B^5+8*B*B+B*B))) := by

  let X : E →L[ℝ] H d := (xCoord d).comp Z
  let Y : E →L[ℝ] H d := (yCoord d).comp Z
  let P : E →L[ℝ] H d := (mCoord d).comp Z
  let Q : E →L[ℝ] H d := (nCoord d).comp Z
  have hPB := jetBound_projection Z (mCoord d) hZ norm_mCoord_le hz hB
  have hQB := jetBound_projection Z (nCoord d) hZ norm_nCoord_le hz hB
  have hXL : ‖X‖ ≤ 1 := norm_comp_contractions _ _ norm_xCoord_le hZ
  have hYL : ‖Y‖ ≤ 1 := norm_comp_contractions _ _ norm_yCoord_le hZ
  have hPL : ‖P‖ ≤ 1 := norm_comp_contractions _ _ norm_mCoord_le hZ
  have hQL : ‖Q‖ ≤ 1 := norm_comp_contractions _ _ norm_nCoord_le hZ
  have hI := (norm_one_le_dimension (d := d)).trans hd
  let U := 42*B^5+8*B*B+B*B
  have h₃ : JetBound (fun v => sandwich (invH (X v)) (P v)-η v (Q v)-ε • (Hermitian.one : H d)) z U :=
    jetBound_stationaryPart X P Q ε hB hI hε hXL hPL hM hQB hX hiX hη hηB
  have h₄ : JetBound (fun v => sandwich (invH (Y v)) (Q v)-η v (P v)-ε • (Hermitian.one : H d)) z U :=
    jetBound_stationaryPart Y Q P ε hB hI hε hYL hQL hN hPB hY hiY hη hηB
  have hc₃ := contDiffAt_stationaryPart ε X.contDiff.contDiffAt P.contDiff.contDiffAt Q.contDiff.contDiffAt hη hX
  have hc₄ := contDiffAt_stationaryPart ε Y.contDiff.contDiffAt Q.contDiff.contDiffAt P.contDiff.contDiffAt hη hY
  exact jetBound_pairHilbert hc₃ hc₄ h₃ h₄

lemma jetBound_kktGiven_oai (Z : E →L[ℝ] Vars d) {S : E → H d}
    {η : E → H d →L[ℝ] H d} {z : E} {ε B : ℝ}
    (hZ : ‖Z‖ ≤ 1) (hz : ‖Z z‖ ≤ B) (hB : 1 ≤ B) (hd : (d:ℝ)+1 ≤ B) (hε : |ε| ≤ B)
    (hX : xCoord d (Z z) ∈ pd d) (hY : yCoord d (Z z) ∈ pd d)
    (hiX : ‖invH (xCoord d (Z z))‖ ≤ B) (hiY : ‖invH (yCoord d (Z z))‖ ≤ B)
    (hM : ‖mCoord d (Z z)‖ ≤ 1) (hN : ‖nCoord d (Z z)‖ ≤ 1)
    (hS : ContDiffAt ℝ 3 S z) (hη : ContDiffAt ℝ 3 η z)
    (hSB : JetBound S z B) (hηB : JetBound η z B) :
    JetBound (fun v => kktSystem ε (S v) (η v) (Z v)) z (300*B^5) := by
  have ht := jetBound_tracePart Z hZ hz hB hd
  have hp := jetBound_kktPrimal Z hZ hz hB hd hε hX hY hiX hiY hM hN hS hη hSB hηB
  have hy := jetBound_kktDual Z hZ hz hB hd hε hX hY hiX hiY hM hN hS hη hSB hηB
  have hc := contDiffAt_kktGiven ε hS hη Z.contDiff.contDiffAt hX hY
  have hb := ht.prod hc.fst hc.snd (hp.prod hc.snd.fst hc.snd.snd hy)
  have he : JetBound (fun v => kktSystem ε (S v) (η v) (Z v)) z
      (2*B*B+1+(2*((B*B+6*B^4+B+8*B*B)+(B*B+6*B^4+B+8*B*B))+
      2*((42*B^5+8*B*B+B*B)+(42*B^5+8*B*B+B*B)))) := hb
  exact he.mono (kktJet_numeric hB)
end
end CurrentKS.Variational

end OAI
end

theorem solution.{u_1} : type_of% @OAI.CurrentKS.Variational.jetBound_kktGiven_oai.{u_1} := @OAI.CurrentKS.Variational.jetBound_kktGiven_oai.{u_1}
