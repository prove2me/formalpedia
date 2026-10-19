-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T07:28:41.209912+00:00
-- url     : https://prove2.me/submissions/4992ce7b-272d-4e3b-90fc-be1086b773cd

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B277
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_AllocatedModelPhysicalExpansionIdentity_exists_native_source_s2
import Theorems.Thm_OAI_Erdos3_goodKernelUniformCandidate_spec_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SampledNativeModel
namespace OAI

section

namespace Erdos3

open scoped BigOperators

attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem nativeCorrelation_restrict_model {A σ : Type*}
    (S : Finset A) (hS : S.Nonempty)
    (w : σ → ℕ) (degree : ℕ) (p : ℝ) (sample : A → σ → ℤ)
    (f twist : A → ℂ)
    (V : NativeSampleCorrelation w degree p S sample
      (fun x => f x * twist x))
    (hV : V.test.normBound ≤ 1) :
    ∃ G : S → ℂ, Nonempty (NativeSampleModel w degree p (fun x => sample x.val) G) ∧
      Real.exp (-p) ≤ ‖(FiniteProbabilityWeights.uniformFinset S hS).correlation (fun x => f x.val)
        (fun x => star (twist x.val) * G x)‖ := by
  let G : S → ℂ := fun x => V.test.eval (sample x.val)
  refine ⟨G, ⟨?_⟩, ?_⟩
  · exact {
      L := V.L
      dim := V.dim
      model := V.model
      test := V.test
      norm := hV
      complexity := V.complexity
      eval := fun _ => rfl }
  have hc := V.correlation
  rw [← FiniteProbabilityWeights.uniformFinset_complexMean S hS
    (fun x => (f x * twist x) * star (V.test.eval (sample x)))] at hc
  simpa only [G, FiniteProbabilityWeights.correlation, FiniteProbabilityWeights.complexMean,
    star_mul, star_star, mul_assoc, mul_left_comm, mul_comm] using hc

end Erdos3

end

section

namespace Erdos3.NativeSampleModel

open CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

attribute [instance] VerticalExpansion.finite

end Erdos3.NativeSampleModel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.PhysicalSpatialScales
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem trimmedSpatial_scale_ratio {X : Type*} {B τ : ℝ} (hB : 0 ≤ B)
    (N modulus : X → ℕ) (x : X) :
    trimmedSpatialRootScale τ N modulus x =
      (1 + B) * trimmedSpatialSlopeScale B τ N modulus x := by
  have hb : 1 + B ≠ 0 := ne_of_gt (by linarith)
  unfold trimmedSpatialRootScale trimmedSpatialSlopeScale
  field_simp

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalAmbientVolumeRatio
namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators

theorem physicalSpatial_uniform_volume {X α : Type*} [Fintype X] [Fintype α]
    (H T : X → ℝ) {W L : ℝ} (hL : L ≠ 0) (hscale : ∀ d, H d = (1 + W) * T d) :
    (∏ d, ∏ _i : Unit ⊕ α, H d) =
      (((1 + W) / L) ^ Fintype.card α) ^ Fintype.card X *
        ∏ d, ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
  have hrow (d) : (∏ _i : Unit ⊕ α, H d) =
      ((1 + W) / L) ^ Fintype.card α * ∏ i, physicalSpatialOutputScale α (H d) (T d) L i := by
    simp only [Fintype.prod_sum_type, physicalSpatialOutputScale, Sum.elim_inl, Sum.elim_inr,
      Finset.prod_const, Finset.card_univ, Fintype.card_unique, pow_one]
    have he : (1 + W) / L * (L * T d) = H d := by rw [hscale d]; field_simp
    rw [mul_left_comm _ (H d), ← mul_pow, he]
    simp only [Fintype.card_sum, Fintype.card_unique, pow_add, pow_one]
  simp_rw [hrow]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, Finset.card_univ]

end Erdos3.BooleanCubeKernel

end

section

namespace Erdos3.BooleanCubeKernel

open scoped BigOperators Classical

theorem physicalSpatial_ambient_volume_ratio {X : Type*} [Fintype X]
    (dim : ℕ) (N H T : X → ℝ) {W L : ℝ}
    (hL : 0 < L) (hH : ∀ x, 0 < H x) (hT : ∀ x, 0 < T x)
    (hscale : ∀ x, H x = (1 + W) * T x) :
    (∏ x, N x) ^ (dim + 1) /
        (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i) =
      (∏ x, (N x / H x) ^ (dim + 1)) * (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hvolume : 0 < ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i :=
    Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ => physicalSpatialOutputScale_pos
      (Fin dim) (hH x) (hT x) hL i))
  have hbase : (∏ x, H x) ^ (dim + 1) ≠ 0 :=
    (pow_pos (Finset.prod_pos (fun x _ => hH x)) _).ne'
  have hvol := physicalSpatial_uniform_volume (α := Fin dim) H T hL.ne' hscale
  have hvol' : (∏ x, H x) ^ (dim + 1) =
      (((1 + W) / L) ^ dim) ^ Fintype.card X *
        (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (H x) (T x) L i) := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_sum, Fintype.card_unique,
      Fintype.card_fin, Nat.add_comm 1 dim, ← Finset.prod_pow] using hvol
  have hratio : (∏ x, (N x / H x) ^ (dim + 1)) =
      (∏ x, N x) ^ (dim + 1) / (∏ x, H x) ^ (dim + 1) := by
    rw [Finset.prod_pow, Finset.prod_div_distrib, div_pow]
  rw [hratio]
  apply (div_eq_iff hvolume.ne').2
  rw [mul_assoc, ← hvol', div_mul_cancel₀ _ hbase]

theorem trimmedSpatial_ambient_volume_ratio {X : Type*} [Fintype X]
    (dim : ℕ) (N q : X → ℕ) {W τ L : ℝ}
    (hW : 0 ≤ W) (hτ : 0 < τ) (hL : 0 < L) (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) :
    (∏ x, (N x : ℝ)) ^ (dim + 1) /
        (∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q x)
          (trimmedSpatialSlopeScale W τ N q x) L i) =
      (∏ x, (8 * (q x : ℝ) / τ) ^ (dim + 1)) * (((1 + W) / L) ^ dim) ^ Fintype.card X := by
  have hscales (x : X) := trimmedSpatial_scales_pos hW hτ N q x (hN x) (hq x)
  rw [physicalSpatial_ambient_volume_ratio dim (fun x => (N x : ℝ))
    (trimmedSpatialRootScale τ N q) (trimmedSpatialSlopeScale W τ N q) hL
    (fun x => (hscales x).1) (fun x => (hscales x).2) (trimmedSpatial_scale_ratio (τ := τ) hW N q)]
  congr 1
  apply Finset.prod_congr rfl
  intro x _
  congr 1
  have hn : (N x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hN x).ne'
  have hq' : (q x : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hq x).ne'
  unfold trimmedSpatialRootScale
  field_simp [hn, hq', hτ.ne']

end Erdos3.BooleanCubeKernel

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.NormalizedNativeUniformBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

attribute [local instance] NativeSampleModel.lie NativeSampleModel.algebra
  NativeSampleModel.topology NativeSampleModel.topologicalAdd
  NativeSampleModel.continuousSMul NativeSampleModel.hausdorff

namespace VectorPolynomial

theorem normalized_native_detection_mono
    {X : Type*} [Fintype X] {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)]
    (N : X → ℕ) (p : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
    {Y : Type*} [Fintype Y] (sample : Y → X → ℤ) (r : FiniteProbabilityWeights Y)
    (signal : Y → ℂ) (s : ℕ)
    {periodCap coverCap periodCap' coverCap' C C' : ℝ} {L L' : ℝ≥0}
    (hperiod : periodCap ≤ periodCap') (hcover : coverCap ≤ coverCap')
    (hL : L ≤ L') (hC : C ≤ C')
    (hdetect : ∃ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap coverCap L,
      ∃ f : Y → ℂ,
        Nonempty (NativeSampleModel (fun _ : X => 1) s C sample f) ∧
        Real.exp (-C) ≤ ‖r.correlation signal (fun u => star (W.eval N p (sample u)) * f u)‖) :
    ∃ W : NormalizedPolynomialTwist X (Σ j, J j) periodCap' coverCap' L',
      ∃ f : Y → ℂ,
        Nonempty (NativeSampleModel (fun _ : X => 1) s C' sample f) ∧
        Real.exp (-C') ≤ ‖r.correlation signal (fun u => star (W.eval N p (sample u)) * f u)‖ := by
  obtain ⟨W, f, ⟨F⟩, hc⟩ := hdetect
  exact ⟨W.mono hperiod hcover hL, f, ⟨F.weaken hC⟩,
    (Real.exp_le_exp.mpr (neg_le_neg hC)).trans hc⟩

end VectorPolynomial
end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedModularGeneralNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule BooleanCubeKernel
open scoped BigOperators Classical

theorem finiteProductPower_exponential_bound {X : Type*} [Fintype X]
    (f : X → ℝ) {B D : ℝ} (hB : 0 ≤ B) (hf0 : ∀ x, 0 ≤ f x)
    (hf : ∀ x, f x ≤ Real.exp B) (hX : (Fintype.card X : ℝ) ≤ D) (n : ℕ) :
    (∏ x, f x ^ n) ≤ Real.exp ((n : ℝ) * D * B) := by
  calc
    _ ≤ ∏ _x : X, (Real.exp B) ^ n := Finset.prod_le_prod
      (fun x _ => pow_nonneg (hf0 x) _) (fun x _ => pow_le_pow_left₀ (hf0 x) (hf x) _)
    _ = Real.exp ((Fintype.card X : ℝ) * ((n : ℝ) * B)) := by
      rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    _ ≤ _ := Real.exp_le_exp.mpr (calc
      _ ≤ D * ((n : ℝ) * B) := mul_le_mul_of_nonneg_right hX (mul_nonneg (Nat.cast_nonneg _) hB)
      _ = _ := by ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open BooleanCubeKernel
open scoped BigOperators Classical

theorem physicalAmbientVolume_log_bound {X : Type*} [Fintype X] [DecidableEq X]
    (dim : ℕ) (N q : X → ℕ) {W τ L D V Q E : ℝ}
    (hW : 0 ≤ W) (hL : 1 ≤ L)
    (hV : 0 ≤ V) (hQ : 0 ≤ Q) (hE : 0 ≤ E)
    (hWscale : W ≤ Real.exp V * L)
    (hX : (Fintype.card X : ℝ) ≤ D)
    (hN : ∀ x, 0 < N x) (hq : ∀ x, 0 < q x) (hτ : 0 < τ)
    (hqexp : ∀ x, (q x : ℝ) ≤ Real.exp Q) (hτexp : 1 / τ ≤ Real.exp E) :
    let volume := ∏ x, ∏ i, physicalSpatialOutputScale (Fin dim) (trimmedSpatialRootScale τ N q x)
      (trimmedSpatialSlopeScale W τ N q x) L i
    (((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) ∧
    ((integerBoxCubeCount N dim : ℝ) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E)) := by
  intro volume
  have hS : (0 : ℝ) < L := zero_lt_one.trans_le hL
  have hscales (x : X) := trimmedSpatial_scales_pos hW hτ N q x (hN x) (hq x)
  have hvolume : 0 < volume := Finset.prod_pos (fun x _ => Finset.prod_pos (fun i _ =>
    physicalSpatialOutputScale_pos (Fin dim) (hscales x).1 (hscales x).2 hS i))
  have hscalar (x : X) : 8 * (q x : ℝ) / τ ≤ Real.exp (8 + Q + E) := by
    calc
      _ = (8 * (q x : ℝ)) * (1 / τ) := by ring
      _ ≤ (Real.exp 8 * Real.exp Q) * Real.exp E := mul_le_mul
        (mul_le_mul (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8)
          (hqexp x) (Nat.cast_nonneg _) (Real.exp_pos _).le)
        hτexp (div_nonneg zero_le_one hτ.le) (by positivity)
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hfirst : (∏ x, (8 * (q x : ℝ) / τ) ^ (dim + 1)) ≤
      Real.exp ((dim + 1 : ℕ) * D * (8 + Q + E)) :=
    finiteProductPower_exponential_bound (fun x => 8 * (q x : ℝ) / τ)
      (by linarith only [hQ, hE]) (fun x => by positivity) hscalar hX (dim + 1)
  have hratio0 : 0 ≤ (1 + W) / (L : ℝ) := div_nonneg (by linarith [hW]) hS.le
  have hratio : (1 + W) / (L : ℝ) ≤ Real.exp (V + 1) :=
    calc
      _ ≤ 1 + Real.exp V := (div_le_iff₀ hS).mpr (by nlinarith only [hL, hWscale])
      _ ≤ _ := one_add_le_exp_succ hV le_rfl
  have hinner := pow_le_exp_mul_of_le_exp hratio0 hratio (by linarith only [hV]) dim
    (le_refl (dim : ℝ))
  have houter := pow_le_exp_mul_of_le_exp (pow_nonneg hratio0 dim) hinner
    (mul_nonneg (Nat.cast_nonneg _) (by linarith only [hV])) (Fintype.card X) hX
  have hsecond : (((1 + W) / (L : ℝ)) ^ dim) ^ Fintype.card X ≤
      Real.exp ((dim : ℕ) * D * (V + 1)) := by
    apply houter.trans_eq
    congr 1
    ring
  have hphysical : (∏ x, (N x : ℝ)) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E) := by
    dsimp only [volume]
    rw [trimmedSpatial_ambient_volume_ratio dim N q hW hτ hS hN hq]
    apply (mul_le_mul hfirst hsecond (pow_nonneg (pow_nonneg hratio0 dim) _) (Real.exp_pos _).le).trans_eq
    rw [← Real.exp_add]
    rfl
  have hbox : ((integerBox N).card : ℝ) ^ (dim + 1) / volume ≤
      Real.exp (allocatedAmbientNormalizationLog dim D V Q E) := by
    simpa only [card_integerBox, Nat.cast_prod] using hphysical
  have hcubes : (integerBoxCubeCount N dim : ℝ) ≤ ((integerBox N).card : ℝ) ^ (dim + 1) := by
    exact_mod_cast integerBoxCubeCount_upper N dim
  exact ⟨hbox, (div_le_div_of_nonneg_right hcubes hvolume.le).trans hbox⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalSlicedSourcePositivity
namespace OAI

section

namespace Erdos3

theorem slicedSource_transfer_gain {gain ε Z projected fine coarse model : ℝ}
    (hgain : 0 < gain) (hε : ε ≤ gain / 32) (hZ : 1 / 2 ≤ Z)
    (hprojected : gain / 2 - ε ≤ projected)
    (hfine : Z * (projected - ε) ≤ fine)
    (hcoarse : fine - ε ≤ coarse) (hmodel : coarse - ε ≤ model) :
    gain / 8 ≤ model := by
  have hnonneg : 0 ≤ projected - ε := by linarith only [hgain, hε, hprojected]
  have hhalf := (mul_le_mul_of_nonneg_right hZ hnonneg).trans hfine
  linarith only [hgain, hε, hprojected, hhalf, hcoarse, hmodel]

theorem slicedSource_transfer_exp {p E Z projected fine coarse model : ℝ}
    (hE : p + 32 ≤ E) (hZ : 1 / 2 ≤ Z)
    (hprojected : Real.exp (-p) / 2 - Real.exp (-E) ≤ projected)
    (hfine : Z * (projected - Real.exp (-E)) ≤ fine)
    (hcoarse : fine - Real.exp (-E) ≤ coarse)
    (hmodel : coarse - Real.exp (-E) ≤ model) :
    Real.exp (-(p + 8)) ≤ model := by
  have heps : Real.exp (-E) ≤ Real.exp (-p) / 32 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 32)).mpr
    calc
      _ ≤ Real.exp (-E) * Real.exp 32 := mul_le_mul_of_nonneg_left
        (by linarith [Real.add_one_le_exp (32 : ℝ)] : (32 : ℝ) ≤ Real.exp 32) (Real.exp_pos _).le
      _ = Real.exp (-E + 32) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith only [hE])
  have hsource := slicedSource_transfer_gain (Real.exp_pos (-p)) heps hZ hprojected hfine hcoarse hmodel
  apply le_trans _ hsource
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8)).mpr
  calc
    _ ≤ Real.exp (-(p + 8)) * Real.exp 8 := mul_le_mul_of_nonneg_left
      (by linarith [Real.add_one_le_exp (8 : ℝ)] : (8 : ℝ) ≤ Real.exp 8) (Real.exp_pos _).le
    _ = Real.exp (-p) := by rw [← Real.exp_add]; congr 1; ring

theorem slicedSource_transfer_combined_exp {p E Z model : ℝ}
    (hE : p + 32 ≤ E) (hZ : 1 / 2 ≤ Z)
    (hsource : Z * (Real.exp (-p) / 2 - Real.exp (-E) - Real.exp (-E)) -
      Real.exp (-E) - Real.exp (-E) ≤ model) :
    Real.exp (-(p + 8)) ≤ model := by
  exact slicedSource_transfer_exp hE hZ le_rfl le_rfl le_rfl hsource

theorem slicedSource_selected_gain_exp {p δ Cmodel Cspatial M S : ℝ}
    (hδ : Real.exp (-(p + 8)) ≤ δ) (hCmodel : 0 < Cmodel) (hCspatial : 0 < Cspatial)
    (hmodel : Cmodel ≤ Real.exp M) (hspatial : Cspatial ≤ Real.exp S) :
    Real.exp (-(p + 8 + M + S)) ≤ δ / (Cmodel * Cspatial) := by
  apply (le_div_iff₀ (mul_pos hCmodel hCspatial)).mpr
  calc
    _ ≤ Real.exp (-(p + 8 + M + S)) * (Real.exp M * Real.exp S) :=
      mul_le_mul_of_nonneg_left (mul_le_mul hmodel hspatial hCspatial.le (Real.exp_nonneg _))
        (Real.exp_nonneg _)
    _ = Real.exp (-(p + 8)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ δ := hδ

end Erdos3

end

section

namespace Erdos3

theorem canonicalSlicedSource_transfer_exp
    {p gain Z Pproj target Ecoarse lossTarget model : ℝ}
    (hgain : Real.exp (-p) / 2 ≤ gain) (hZ : 1 / 2 ≤ Z)
    (hPproj : p + 32 ≤ Pproj) (htarget : p + 32 ≤ target)
    (hEcoarse : p + 32 ≤ Ecoarse) (hlossTarget : p + 32 ≤ lossTarget)
    (hsource : Z * (gain - Real.exp (-Pproj) - Real.exp (-target)) -
      Real.exp (-Ecoarse) - Real.exp (-lossTarget) ≤ model) :
    Real.exp (-(p + 8)) ≤ model := by
  have hZnonneg : 0 ≤ Z := le_trans (by norm_num) hZ
  have hproj : Real.exp (-Pproj) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg hPproj)
  have ht : Real.exp (-target) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg htarget)
  have hc : Real.exp (-Ecoarse) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg hEcoarse)
  have hl : Real.exp (-lossTarget) ≤ Real.exp (-(p + 32)) :=
    Real.exp_le_exp.mpr (neg_le_neg hlossTarget)
  apply slicedSource_transfer_combined_exp (E := p + 32) le_rfl hZ
  exact (sub_le_sub (sub_le_sub
    (mul_le_mul_of_nonneg_left (sub_le_sub (sub_le_sub hgain hproj) ht) hZnonneg)
    hc) hl).trans hsource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalProjectedNativeSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

variable (e : {a // allocatedGridAxis (I := I) U b S.value a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))))

variable {T : Type*} [Fintype T] (a : T → ℂ)
variable (f : T → Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ)
local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "volume" => ∏ z, ∏ i, physicalSpatialOutputScale (Fin (s + 1))
  (trimmedSpatialRootScale τ N stride z) (trimmedSpatialSlopeScale W τ N stride z) S.value i
local notation "twist" => allocatedRecenteredSpatialTwist (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x N mesh base label

variable [∀ i, NeZero (N i)]
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem AllocatedModelPhysicalExpansionIdentity.exists_uniform_canonical_normalized_native_model_of_positive_source
    (g : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period))) →
      T → (∀ a, (e a).Term) → Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ)
    (hidentity : AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm g)
    {L : ℝ≥0} (hg : ∀ label i k site, LipschitzWith L (g label i k site))
    (hgb : ∀ label i k site z, ‖g label i k site z‖ ≤ 1)
    {Nt V Cc Hs : {a // allocatedGridAxis (I := I) U b S.value a} → ℝ} {Lg : ℝ≥0}
    (he : ∀ a, (e a).Bounds (Nt a) (V a) (Cc a) Lg (Hs a))
    (Vmax : ℝ≥0) (hVmax : ∀ a, V a ≤ Vmax)
    (hstride : ∀ z, 0 < stride z)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hV : ∀ z, 0 < widths z) (hZ : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hτ : 0 < τ)
    {pGain Emodel Espatial Pvolume : ℝ}
    (hpGain : 0 ≤ pGain) (hEmodel : 0 ≤ Emodel) (hEspatial : 0 ≤ Espatial)
    (hPvolume : 0 ≤ Pvolume)
    (hdim : (nX : ℝ) ≤ pGain + 8 + Emodel + Espatial + Pvolume)
    (hmass : (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)), ∑ i, ∑ k,
      ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
        allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
        coverSiteCoefficient e k‖) ≤ Real.exp Emodel)
    (hpositive : Real.exp (-(pGain + 8)) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re)
    {pGeometry Ecoarse analytic : ℝ}
    (hpGeometry : 0 ≤ pGeometry) (hEcoarse : 0 ≤ Ecoarse) (hanalytic : 0 ≤ analytic)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hvolumeLog : allocatedAmbientNormalizationLog (s + 1) (nX : ℝ) pGeometry pGeometry pGeometry ≤ Pvolume)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hspatialLog : coarseSpatialPartitionLog (allocatedEarlyCoarseInput m (s + 1) (pGeometry + Ecoarse)) ≤ Espatial)
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    (hLanalytic : ((L * (period * Vmax ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a}) : ℝ≥0) : ℝ) ≤ Real.exp analytic)
    {Bbudget : ℝ} (hBbudget : 0 ≤ Bbudget)
    (hGeometryBudget : pGeometry ≤ Bbudget) (hCoarseBudget : Ecoarse ≤ Bbudget)
    (hAnalyticBudget : analytic ≤ Bbudget) (hGainBudget : pGain ≤ Bbudget)
    (hMassBudget : Emodel ≤ Bbudget) (hSpatialBudget : Espatial ≤ Bbudget)
    (hVolumeBudget : Pvolume ≤ Bbudget)
    (hCoverBudget : (period : ℝ) * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a} ≤ Real.exp Bbudget) :
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  intro Anorm Anative A budget
  have hnumeric := (Classical.choose_spec (exists_normalizedNative_uniform_budget m Anorm Anative)).2
    hBbudget ⟨hpGeometry, hGeometryBudget⟩ ⟨hEcoarse, hCoarseBudget⟩ ⟨hanalytic, hAnalyticBudget⟩
    ⟨hpGain, hGainBudget⟩ ⟨hEmodel, hMassBudget⟩ ⟨hEspatial, hSpatialBudget⟩ ⟨hPvolume, hVolumeBudget⟩
    (le_refl Bbudget) (hXGeometry.trans hGeometryBudget)
  have hvolume := (physicalAmbientVolume_log_bound (s + 1) N stride hW
    (by exact_mod_cast Nat.succ_le_of_lt S.positive : (1 : ℝ) ≤ S.value)
    hpGeometry hpGeometry hpGeometry hWGeometry
    (by simp only [Fintype.card_fin]; exact le_rfl : (Fintype.card (Fin nX) : ℝ) ≤ nX)
    (fun i => Nat.pos_of_ne_zero (NeZero.ne (N i))) hstride hτ hstrideGeometry hτGeometry).2
  have hvolumeRatio : (integerBoxCubeCount N (s + 1) : ℝ) / volume ≤ Real.exp Pvolume :=
    hvolume.trans (Real.exp_le_exp.mpr hvolumeLog)
  have hmodulusGeometry : spatialModulus ≤ M ^ (m + 1) := by
    rw [hcanonical]
    exact kernelPeriodCandidate_le _ _
  have hperiod : integerScalarLattice (Unit ⊕ Fin (s + 1)) (spatialModulus : ℤ) ≤
      pivotFullImage (selectedSpatialPivot (fun g => (0 : ℤ) + (x g none : ℤ))
        (scalarCubeDifferenceMatrix x) selection)
        (selectedSpatialFreeColumns (fun g => (0 : ℤ) + (x g none : ℤ))
          (scalarCubeDifferenceMatrix x) selection) := by
    rw [hcanonical]
    exact (goodKernelUniformCandidate_spec_s2.{0,uG,0} selection x hx m).1 _
  have hpartition := allocatedEarlyRecenteredMesh_partition_budget m (Fin nX) selection
    hpGeometry hEcoarse hGGeometry (by simpa using hXGeometry) hM hMGeometry hmodulusGeometry
  rw [← hmeshEarly] at hpartition
  have hmargin : 3 + 2 * mesh ≤ 4 := by linarith only [hpartition.2.1]
  have hspatial := hpartition.2.2.2.trans (Real.exp_le_exp.mpr hspatialLog)
  have hgain := slicedSource_selected_gain_exp (δ := Real.exp (-(pGain + 8)))
    (Cmodel := Real.exp Emodel) (Cspatial := Real.exp Espatial) le_rfl
    (Real.exp_pos _) (Real.exp_pos _) le_rfl le_rfl
  obtain ⟨cover, hcover, hcoverBound, F, hF, hFb, cell, t, hψ, Vnative, hVnative, hcorrelation⟩ :=
    hidentity.exists_native_source_s2 B U b S x y₀ q d period r hr hb o bW e a f p hm
      spatialModulus stride N wholeReference label hM selection hx hW base cells g hg hgb he Vmax hVmax
      hstride hpartition.1 hmargin hbudget hperiod hV hZ signal hsignal hzero hτ
      (show 0 ≤ pGain + 8 + Emodel + Espatial by positivity) hPvolume hdim hvolumeRatio
      (Real.exp_pos _) (Real.exp_pos _) (Real.exp_pos _) hmass hspatial hpositive hgain
  have hN (i) : 0 < N i := Nat.pos_of_ne_zero (NeZero.ne (N i))
  obtain ⟨hperiodPos, hperiodBound, mask, H, hmask, hH, hLip, hfactor⟩ :=
    (Classical.choose_spec (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))).2
      B U b S selection hpGeometry hEcoarse hanalytic hGGeometry
      (by simpa only [Fintype.card_fin] using hXGeometry) hdimGeometry hM hMGeometry hmodulusGeometry
      ⟨mesh, hpartition.1.le⟩ hmeshEarly stride N hN hstride hstrideGeometry hτ hτGeometry
      wholeReference x base label cell.val t ∅ (F ∅) (hF ∅) (hFb ∅) hLanalytic
  let twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp (((m + 1 : ℕ) : ℝ) * pGeometry + Fintype.card (Fin nX) * pGeometry))
      (period * (Vmax : ℝ) ^ Fintype.card {a // allocatedGridAxis (I := I) U b S.value a})
      ⟨Real.exp ((pGeometry + Ecoarse + analytic + Anorm) ^ Anorm), Real.exp_nonneg _⟩ := {
    modulus := residueRefinedPeriod spatialModulus stride
    modulus_pos := hperiodPos
    modulus_bound := hperiodBound
    cover := cover
    cover_pos := hcover
    cover_bound := hcoverBound
    mask := mask
    mask_bound := hmask
    smooth := H
    smooth_bound := hH
    smooth_lipschitz := hLip }
  have heq (u : (Fin nX) → ℤ) :
      twist cell.val t ∅ u * F ∅ (physicalGridFactorInput cover p (fun i => (u i : ℝ))) =
        twistData.eval N p u := hfactor u _
  let Vnormalized : NativeSampleCorrelation (fun _ : Fin nX => 1) s
      ((pGain + 8 + Emodel + Espatial + Pvolume + 2) ^ Anative)
      (integerBox N) id (fun u => signal u * twistData.eval N p u) :=
    { Vnative with correlation := by simpa only [heq] using Vnative.correlation }
  obtain ⟨Fnative, hmodel, hcorr⟩ := nativeCorrelation_restrict_model
    (integerBox N) (integerBox_nonempty N) (fun _ : Fin nX => 1) s _ id
    signal (twistData.eval N p) Vnormalized hVnative
  apply normalized_native_detection_mono N p (fun u : integerBox N => u.val)
    (FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N))
    (fun u => signal u.val) s ?_ ?_ ?_ hnumeric.2.2.2 ⟨twistData, Fnative, hmodel, hcorr⟩
  · apply Real.exp_le_exp.mpr
    simpa only [Fintype.card_fin] using hnumeric.1
  · exact hCoverBudget.trans (Real.exp_le_exp.mpr hnumeric.2.1)
  · exact Real.exp_le_exp.mpr hnumeric.2.2.1

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
universe uG uI uB uJ

open Module Submodule _root_.Set _root_.OAI.Set BooleanCubeKernel
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type uG} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type uI} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type uB) [∀ a, Fintype (B a)]
variable {J : Fin m → Type uJ} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {s nX : ℕ}
local notation "rowSets" => (fun j : Fin m => boundedBooleanJetRows (Fin (s + 1)) (Fin.val j + 1))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin (s + 1)) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin (s + 1))))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin (s + 1)) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1)) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

attribute [local instance] ScalarSiteExpansion.termFinite
attribute [local instance 2000] fullGridCoverAxisDecidableEq

local notation "LongSpace" => ((JetAmbientIndex (fun _ : Fin m => Unit) J → UnitAddCircle) × ((Σ j, J j) → UnitAddCircle))
local notation "GridSpace" => ((Σ j, J j) → UnitAddCircle)

variable (p : ∀ j, VectorPolynomial (Fin nX) ℝ (J j → ℝ))
variable (hm : ∀ j e, coefficients (p j) e ∈ U j)

variable (spatialModulus : ℕ) [NeZero spatialModulus] (stride N : (Fin nX) → ℕ)
variable (wholeReference :
  (PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) → PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin (s + 1))
  (allocatedPrincipalSides B U b S))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin (s + 1)) → ZMod (residueRefinedPeriod spatialModulus stride)) {M : ℕ} (hM : 0 < M) (selection : Fin (s + 1) ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
variable {W τ ξ mesh : ℝ} (hW : 0 ≤ W) (base : (Fin nX) → ℤ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) (Fin nX) stride))
local notation "window" => spatialWindow (α := Fin (s + 1)) (trimmedSpatialRootScale τ N stride) 4
local notation "widths" => narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N
local notation "reconstruct" => allocatedWholeResidueReconstruction B U b S (Fin nX) spatialModulus stride wholeReference x base label

variable [∀ i, NeZero (N i)]
attribute [local instance] NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_allocatedCanonical_finite_source_native_s2_oai
    (signal : ((Fin nX) → ℤ) → ℂ)
    (hsignal : ∀ u ∈ integerBox N, ‖signal u‖ ≤ 1)
    (hzero : ∀ u, u ∉ integerBox N → signal u = 0)
    (hstride : ∀ z, 0 < stride z) (hτ : 0 < τ) (hξ : 0 < ξ)
    (hbudget : allocatedPhysicalRootBudget B U b S (fun _ => 0) ≤ W)
    (hZmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells widths z)
    {P D pgrid v Fmodel Prho Pk target Banalytic pGeometry Ecoarse pGain : ℝ}
    (hP : 0 ≤ P) (hD : D ∈ Icc 0 P) (hgrid : pgrid ∈ Icc 0 P) (hv : v ∈ Icc 0 P)
    (hFmodel : Fmodel ∈ Icc 0 P) (hPrho : Prho ∈ Icc 0 P) (hPk : Pk ∈ Icc 0 P)
    (htarget : target ∈ Icc 0 P) (hBanalytic : Banalytic ∈ Icc 0 P)
    (hGeometry : pGeometry ∈ Icc 0 P) (hEcoarse : Ecoarse ∈ Icc 0 P)
    (hpGain : pGain ∈ Icc 0 P)
    (hGGeometry : (Fintype.card G : ℝ) ≤ pGeometry)
    (hXGeometry : (nX : ℝ) ≤ pGeometry) (hdimGeometry : ((s + 2 : ℕ) : ℝ) ≤ pGeometry)
    (hMGeometry : (M : ℝ) ≤ Real.exp pGeometry)
    (hWGeometry : W ≤ Real.exp pGeometry * S.value)
    (hcanonical : spatialModulus = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
    (hmeshEarly : mesh = allocatedEarlyRecenteredMesh (Fin nX) selection M spatialModulus pGeometry Ecoarse)
    (hstrideGeometry : ∀ i, (stride i : ℝ) ≤ Real.exp pGeometry)
    (hτGeometry : 1 / τ ≤ Real.exp pGeometry)
    {gain Z Pproj coarseTarget lossTarget Op Hgrid : ℝ}
    (hgain : Real.exp (-pGain) / 2 ≤ gain) (hZ : 1 / 2 ≤ Z)
    (hPproj : pGain + 32 ≤ Pproj) (hcoarseTarget : pGain + 32 ≤ coarseTarget)
    (hEcoarseGain : pGain + 32 ≤ Ecoarse) (hlossTarget : pGain + 32 ≤ lossTarget) :
    let Amass := Classical.choose (exists_allocatedAffineModelMass_budget m (s + 1))
    let Aanalytic := Classical.choose (exists_allocatedAffineAnalytic_budget m (s + 1))
    let Emodel := (D + pgrid + v + Fmodel + Prho + Pk + target + Amass) ^ Amass
    let analytic := (D + pgrid + v + Fmodel + Prho + Pk + target + Banalytic + Aanalytic) ^ Aanalytic
    let Vgrid : ℝ≥0 := ⟨Real.exp Op, Real.exp_nonneg _⟩
    (∃ e : {a // grid a} → ScalarSiteExpansion.{0,0} (Finset (Fin (s + 1))),
      (∀ z, (e z).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op) Vgrid (Real.exp Hgrid)) ∧
      ∃ k : ℕ, ∃ (a : (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) → ℂ)
        (f : (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) →
          Finset (Fin (s + 1)) → (LayerSamplerAxis I n → ℝ) → ℂ),
        (∑ label : Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)),
          ∑ i, ∑ kg, ‖((2 : ℂ) ^ Fintype.card (Finset (Fin (s + 1))) *
            allocatedProductMaskedIdealCoefficient B U b S rowSets x y₀ q d period a label i) *
            coverSiteCoefficient e kg‖) ≤ Real.exp Emodel ∧
        (∃ Lanalytic : ℝ≥0,
          ((Lanalytic * ((period : ℝ≥0) * Vgrid ^ Fintype.card {a // grid a}) : ℝ≥0) : ℝ) ≤
            Real.exp analytic ∧
          (period : ℝ) * (Real.exp Op) ^ Fintype.card {a // grid a} ≤ Real.exp analytic ∧
          ∃ analyticFactor : (Finset (Fin (s + 1)) → ((∀ j, Fin (n j) → ZMod period) ×
              (∀ j, E j → ZMod period))) →
              (Finset (Fin (s + 1)) × LayerSamplerAxis I n → Fin k) → (∀ z, (e z).Term) →
              Finset (Fin (s + 1)) → LongSpace × GridSpace → ℂ,
            (∀ label i kg site, LipschitzWith Lanalytic (analyticFactor label i kg site)) ∧
            (∀ label i kg site z, ‖analyticFactor label i kg site z‖ ≤ 1) ∧
            AllocatedModelPhysicalExpansionIdentity B U b S x y₀ q d period r hr hb o bW e a f p hm analyticFactor) ∧
        Z * (gain - Real.exp (-Pproj) - Real.exp (-coarseTarget)) -
          Real.exp (-Ecoarse) - Real.exp (-lossTarget) ≤
          (∑ z : cells × window, (selectedResidueCellWeight stride cells widths z.1 : ℂ) *
            allocatedRecenteredResidueWeight (τ := τ) B U b S (Fin nX) spatialModulus stride wholeReference x hM selection hx
              N hW mesh base cells (physicalCubeSiteTest (integerSelfSiteTest (s + 1) signal)) label z.1 z.2.val *
            (allocatedProductChartIdealApproximation B U b S rowSets x y₀ q d period r hr hb o bW a f
              (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)) *
            allocatedFullGridChartModel B U b S rowSets d hb o bW e
              (physicalCubeRowSample U d rows p hm (reconstruct z.1.val z.2.val)))).re) →
    let C := Classical.choose (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)
    let Bbudget := (P + C) ^ C
    let Anorm := Classical.choose (exists_allocatedRecenteredFactor_normalization.{uG,uI,uB,uJ,0,uJ} m (s + 1))
    let Anative := Classical.choose (exists_native_partner_of_physical_cube_mixture_all_degrees.{0} s)
    let A := Classical.choose (exists_normalizedNative_uniform_budget m Anorm Anative)
    let budget := (Bbudget + A) ^ A
    ∃ twistData : NormalizedPolynomialTwist (Fin nX) (Σ j, J j)
      (Real.exp budget) (Real.exp budget) ⟨Real.exp budget, Real.exp_nonneg _⟩,
      ∃ Fnative : integerBox N → ℂ,
        Nonempty (NativeSampleModel (fun _ : Fin nX => 1) s budget
          (fun u : integerBox N => u.val) Fnative) ∧
        Real.exp (-budget) ≤
          ‖(FiniteProbabilityWeights.uniformFinset (integerBox N) (integerBox_nonempty N)).correlation
            (fun u => signal u.val) (fun u => star (twistData.eval N p u.val) * Fnative u)‖ := by
  intro Amass Aanalytic Emodel analytic Vgrid hconstructed C Bbudget Anorm Anative A budget
  let Espatial := coarseSpatialPartitionLog (allocatedEarlyCoarseInput m (s + 1) (pGeometry + Ecoarse))
  let Pvolume := (nX : ℝ) + allocatedAmbientNormalizationLog (s + 1) (nX : ℝ) pGeometry pGeometry pGeometry
  obtain ⟨hPB, hmassB, hanalyticB, hspatialB, hvolumeB, hvolumeLog, hdim⟩ :=
    (Classical.choose_spec (exists_canonicalSlicedNative_input_budget m (s + 1) Amass Aanalytic)).2
      hP hD hgrid hv hFmodel hPrho hPk htarget hBanalytic hGeometry hEcoarse hpGain
      (hXGeometry.trans hGeometry.2)
  obtain ⟨e, he, k, a, f, hmass, hphysical, hsource⟩ := hconstructed
  obtain ⟨Lanalytic, hLanalytic, hCover, analyticFactor, hLip, hbounded, hidentity⟩ := hphysical
  have hpositive : Real.exp (-(pGain + 8)) ≤ (allocatedRecenteredFiniteModelSource (τ := τ) (ξ := ξ) (mesh := mesh)
      B U b S x y₀ q d period r hr hb o bW e a f p hm spatialModulus stride N wholeReference label
      hM selection hx hW base cells (integerSelfSiteTest (s + 1) signal)).re :=
    canonicalSlicedSource_transfer_exp hgain hZ hPproj hcoarseTarget hEcoarseGain hlossTarget hsource
  have hN (i) : 0 < N i := Nat.pos_of_ne_zero (NeZero.ne (N i))
  have hwidths : ∀ z, 0 < widths z := narrowTrimmedSpatialWidths_pos hW hτ hξ N hN
  exact hidentity.exists_uniform_canonical_normalized_native_model_of_positive_source
    B U b S x y₀ q d period r hr hb o bW e a f p hm
    spatialModulus stride N wholeReference label hM selection hx hW base cells
    analyticFactor hLip hbounded he Vgrid (fun _ => le_rfl)
    hstride hbudget hwidths hZmass signal hsignal hzero hτ
    hpGain.1 hmassB.1 hspatialB.1 hvolumeB.1 hdim hmass hpositive
    hGeometry.1 hEcoarse.1 hanalyticB.1 hGGeometry hXGeometry hdimGeometry hMGeometry hWGeometry
    hvolumeLog hcanonical (le_refl Espatial) hmeshEarly hstrideGeometry hτGeometry hLanalytic
    (hP.trans hPB) (hGeometry.2.trans hPB) (hEcoarse.2.trans hPB) hanalyticB.2 (hpGain.2.trans hPB)
    hmassB.2 hspatialB.2 hvolumeB.2 (hCover.trans (Real.exp_le_exp.mpr hanalyticB.2))

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uG, uI, uB, uJ, u_1} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native_s2_oai.{uG, uI, uB, uJ, u_1} := @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonical_finite_source_native_s2_oai.{uG, uI, uB, uJ, u_1}
