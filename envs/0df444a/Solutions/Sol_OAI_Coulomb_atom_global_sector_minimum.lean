-- Prove2me | solution 1 for OAI.Coulomb.atom_global_sector_minimum
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T00:21:45.395134+00:00
-- url     : https://prove2.me/submissions/f0110013-6a15-4d1c-9610-9fc9844b966a

import Mathlib
import Definitions.Def_CoulombRadii
import Definitions.Def_OAIQ062C008
import Theorems.Thm_OAI_Coulomb_atom_strict_binding_attained

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_FermionicCoefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb

open scoped Classical

lemma integral_permute {n : ℕ} (p : Equiv.Perm (Fin n))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Configuration n → E) :
    (∫ x, f (permute p x)) = ∫ x, f x := by
  have h := (permuteIsometry p).measurePreserving.integral_comp
    (permuteIsometry p).toHomeomorph.measurableEmbedding f
  simpa only [permuteIsometry_apply] using h

lemma sign_complex_norm {n : ℕ} (p : Equiv.Perm (Fin n)) :
    ‖((p.sign : ℤ) : ℂ)‖ = 1 := by
  rcases Int.units_eq_one_or (p.sign) with h | h <;> simp [h]

lemma Antisymmetric.norm_permute {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (p : Equiv.Perm (Fin n)) (s : Spins n) :
    ∀ᵐ x ∂volume, ‖ψ.value (s ∘ p) (permute p x)‖ = ‖ψ.value s x‖ := by
  filter_upwards [hψ p s] with x hx
  rw [hx, norm_mul, sign_complex_norm, one_mul]

lemma antisymmetric_expectation_permute {n : ℕ} {ψ : H1Vector n} (hψ : Antisymmetric ψ)
    (p : Equiv.Perm (Fin n)) (f : Configuration n → ℝ) :
    (∑ s, ∫ x, f (permute p x) * ‖ψ.value s x‖^2) =
      ∑ s, ∫ x, f x * ‖ψ.value s x‖^2 := by
  have he : ∀ s, (∫ x, f (permute p x) * ‖ψ.value s x‖^2) =
      ∫ x, f x * ‖ψ.value (s ∘ p) x‖^2 := by
    intro s
    calc
      _ = ∫ x, f (permute p x) * ‖ψ.value (s ∘ p) (permute p x)‖^2 := by
        apply integral_congr_ae
        filter_upwards [hψ.norm_permute p s] with x hx
        rw [hx]
      _ = _ := integral_permute p (fun x => f x * ‖ψ.value (s ∘ p) x‖^2)
  simp_rw [he]
  exact (spinPermEquiv p).sum_comp (fun s => ∫ x, f x * ‖ψ.value s x‖^2)

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_Add
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma Antisymmetric.add {n : ℕ} {ψ φ : H1Vector n}
    (hψ : Antisymmetric ψ) (hφ : Antisymmetric φ) : Antisymmetric (ψ.add φ) := by
  intro p s
  filter_upwards [hψ p s, hφ p s] with x hx hy
  change ψ.value (s ∘ p) (permute p x) + φ.value (s ∘ p) (permute p x) = _
  rw [hx, hy]
  exact (mul_add _ _ _).symm

lemma norm_add_rsmul_sq (u v : ℂ) (t : ℝ) :
    ‖u + (t : ℂ) * v‖^2 =
      (1-t)*‖u‖^2 + (t^2-t)*‖v‖^2 + t*‖u+v‖^2 := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re,
    Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma mass_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ) :
    mass (ψ.add (φ.rsmul t)) =
      (1-t)*mass ψ + (t^2-t)*mass φ + t*mass (ψ.add φ) := by
  unfold mass
  have hiψ := fun s => (ψ.value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have hiφ := fun s => (φ.value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have hiadd := fun s => ((ψ.add φ).value_L2 s).integrable_norm_pow (p := 2) (by decide)
  have heq : ∀ s, (∫ x, ‖(ψ.add (φ.rsmul t)).value s x‖^2) =
      (1-t)*(∫ x, ‖ψ.value s x‖^2) + (t^2-t)*(∫ x, ‖φ.value s x‖^2) +
      t*(∫ x, ‖(ψ.add φ).value s x‖^2) := by
    intro s
    change (∫ x, ‖ψ.value s x + (t : ℂ)*φ.value s x‖^2) = _
    simp_rw [norm_add_rsmul_sq]
    have hsum : Integrable (fun x => (1-t)*‖ψ.value s x‖^2 +
        (t^2-t)*‖φ.value s x‖^2) := ((hiψ s).const_mul _).add ((hiφ s).const_mul _)
    have hadd : Integrable (fun x => t*‖ψ.value s x + φ.value s x‖^2) :=
      (hiadd s).const_mul t
    rw [integral_add hsum hadd,
      integral_add ((hiψ s).const_mul (1-t)) ((hiφ s).const_mul (t^2-t))]
    simp only [integral_const_mul]
    rfl
  simp_rw [heq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma kinetic_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ) :
    kinetic (ψ.add (φ.rsmul t)) =
      (1-t)*kinetic ψ + (t^2-t)*kinetic φ + t*kinetic (ψ.add φ) := by
  unfold kinetic
  have heq : ∀ s a, (∫ x, ‖(ψ.add (φ.rsmul t)).gradient s a x‖^2) =
      (1-t)*(∫ x, ‖ψ.gradient s a x‖^2) +
      (t^2-t)*(∫ x, ‖φ.gradient s a x‖^2) +
      t*(∫ x, ‖(ψ.add φ).gradient s a x‖^2) := by
    intro s a
    have hiψ := (ψ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)
    have hiφ := (φ.partial_L2 s a).integrable_norm_pow (p := 2) (by decide)
    have hiadd := ((ψ.add φ).partial_L2 s a).integrable_norm_pow (p := 2) (by decide)
    change (∫ x, ‖ψ.gradient s a x + (t : ℂ)*φ.gradient s a x‖^2) = _
    simp_rw [norm_add_rsmul_sq]
    have hsum : Integrable (fun x => (1-t)*‖ψ.gradient s a x‖^2 +
        (t^2-t)*‖φ.gradient s a x‖^2) := (hiψ.const_mul _).add (hiφ.const_mul _)
    have hadd : Integrable (fun x => t*‖ψ.gradient s a x + φ.gradient s a x‖^2) :=
      hiadd.const_mul t
    rw [integral_add hsum hadd, integral_add (hiψ.const_mul (1-t)) (hiφ.const_mul (t^2-t))]
    simp only [integral_const_mul]
    rfl
  simp_rw [heq]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

end Coulomb
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_HarmonicInterior
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
theorem dirPartial_mul {f g : Position → ℝ} {x v : Position}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    dirPartial (fun y => f y*g y) v x = f x*dirPartial g v x+g x*dirPartial f v x := by
  change fderiv ℝ (f*g) x v = _
  rw [fderiv_mul hf hg]
  simp [dirPartial]

end NeutralAtom
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_SortedCut
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
noncomputable section
namespace Coulomb

lemma kinetic_congr_ae {n : ℕ} (u v : H1Vector n) (he : ∀ s, u.value s =ᵐ[volume] v.value s) :
    kinetic u=kinetic v := by
  unfold kinetic
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  apply Finset.sum_congr rfl
  intro a ha
  apply integral_congr_ae
  filter_upwards [u.gradient_congr_ae v he s a] with x hx
  rw [hx]

lemma potentialEnergy_congr_ae {n : ℕ} (W : Configuration n → ℝ) (u v : H1Vector n)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) : potentialEnergy W u=potentialEnergy W v := by
  apply Finset.sum_congr rfl
  intro s hs
  apply integral_congr_ae
  filter_upwards [he s] with x hx
  rw [hx]

lemma form_congr_ae {J n : ℕ} (S : Nuclei J) (u v : H1Vector n)
    (he : ∀ s, u.value s =ᵐ[volume] v.value s) : form S u=form S v := by
  change kinetic u-potentialEnergy (nuclearPotential S) u+potentialEnergy pairPotential u =
    kinetic v-potentialEnergy (nuclearPotential S) v+potentialEnergy pairPotential v
  rw [kinetic_congr_ae u v he,potentialEnergy_congr_ae _ u v he,potentialEnergy_congr_ae _ u v he]

end Coulomb
end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_PhysicalBridge
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
noncomputable section
namespace NeutralAtom

lemma flattenConfiguration_measurePreserving (n : ℕ) :
    MeasurePreserving (flattenConfiguration n).toHomeomorph.toMeasurableEquiv :=
  (flattenConfiguration_symm_measurePreserving n).symm

lemma fromH1_weak {n : ℕ} (ψ : Coulomb.H1Vector n) :
    HasWeakGradient (fromH1Wave ψ) (fromH1Gradient ψ) := by
  intro s i a φ hφ hc
  have H := weakDirectional_pullback (flattenConfiguration n)
    (flattenConfiguration_measurePreserving n) (ψ.weak_partial s (i,a))
    (flattenConfiguration_coordinateDirection i a) φ hφ hc
  simpa only [fromH1Wave,fromH1Gradient,mul_comm] using H

lemma asH1_antisymmetric {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) : Coulomb.Antisymmetric (asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1) := by
  intro p s
  have H := (flattenConfiguration_symm_measurePreserving n).quasiMeasurePreserving.ae (hd.1 p s)
  exact H

lemma fromH1_domain {n : ℕ} (ψ : Coulomb.H1Vector n) (ha : Coulomb.Antisymmetric ψ) :
    FormDomain (fromH1Wave ψ) (fromH1Gradient ψ) := by
  refine ⟨?_, fromH1_weak ψ, ?_, ?_, ?_, ?_⟩
  · intro p s
    exact (flattenConfiguration_measurePreserving n).quasiMeasurePreserving.ae (ha p s)
  · intro s
    exact (ψ.value_L2 s).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i a
    exact (ψ.partial_L2 s (i,a)).comp_measurePreserving (flattenConfiguration_measurePreserving n)
  · intro s i
    have H := (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.nuclear_coulomb_integrable_bound s i 0 (by norm_num : (0:ℝ)<1)).1
    change Integrable (fun x : Configuration n => ‖x i-0‖⁻¹*‖fromH1Wave ψ s x‖^2) at H
    simpa only [sub_zero] using H
  · intro s i j hij
    exact (flattenConfiguration_measurePreserving n).integrable_comp_of_integrable
      (ψ.pair_coulomb_integrable_bound s i j hij.ne (by norm_num : (0:ℝ)<1)).1

lemma fromH1_mass {n : ℕ} (ψ : Coulomb.H1Vector n) :
    normSquared (fromH1Wave ψ) = Coulomb.mass ψ := by
  unfold normSquared Coulomb.mass fromH1Wave
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.value s x‖^2)

lemma asH1_mass {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) :
    Coulomb.mass (asH1 ψ g hw hψ hg) = normSquared ψ := by
  unfold normSquared Coulomb.mass asH1
  apply Finset.sum_congr rfl
  intro s _
  exact (flattenConfiguration_symm_measurePreserving n).integral_comp' (fun x => ‖ψ s x‖^2)

lemma coulombPotential_flatten {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (x : Configuration n) :
    coulombPotential Z x = -Coulomb.nuclearPotential (Coulomb.atom Z hZ)
      (flattenConfiguration n x) + Coulomb.pairPotential (flattenConfiguration n x) := by
  classical
  simp [coulombPotential,Coulomb.nuclearPotential,Coulomb.pairPotential,Coulomb.attraction,
    Coulomb.atom,Coulomb.coulombKernel,Finset.sum_filter,Finset.mul_sum,neg_mul]

lemma fromH1_energy {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) (ψ : Coulomb.H1Vector n) :
    energy Z (fromH1Wave ψ) (fromH1Gradient ψ) = Coulomb.form (Coulomb.atom Z hZ) ψ := by
  have hK : (∑ s : Spins n, ∑ i : Fin n, ∑ a : Fin 3,
      ∫ x : Configuration n, ‖fromH1Gradient ψ s i a x‖^2) =
      ∑ s : Coulomb.Spins n, ∑ ia : Fin n × Fin 3,
        ∫ x : Coulomb.Configuration n, ‖ψ.gradient s ia x‖^2 := by
    simp only [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro a _
    exact (flattenConfiguration_measurePreserving n).integral_comp' (fun x => ‖ψ.gradient s (i,a) x‖^2)
  have hV (s : Spins n) :
      (∫ x : Configuration n, coulombPotential Z x * ‖fromH1Wave ψ s x‖^2) =
      -(∫ x, Coulomb.nuclearPotential (Coulomb.atom Z hZ) x * ‖ψ.value s x‖^2) +
        ∫ x, Coulomb.pairPotential x * ‖ψ.value s x‖^2 := by
    simp_rw [coulombPotential_flatten Z hZ]
    change (∫ x, (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) (flattenConfiguration n x) +
      Coulomb.pairPotential (flattenConfiguration n x)) * ‖ψ.value s (flattenConfiguration n x)‖^2) = _
    calc
      _ = ∫ x, (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) x + Coulomb.pairPotential x) * ‖ψ.value s x‖^2 :=
        (flattenConfiguration_measurePreserving n).integral_comp'
          (fun x => (-Coulomb.nuclearPotential (Coulomb.atom Z hZ) x + Coulomb.pairPotential x) * ‖ψ.value s x‖^2)
      _ = _ := ?_

    simp_rw [add_mul,neg_mul]
    have hn : Integrable (fun x => -(Coulomb.nuclearPotential (Coulomb.atom Z hZ) x * ‖ψ.value s x‖^2)) :=
      (ψ.nuclear_integrable (Coulomb.atom Z hZ) s).neg
    have hp : Integrable (fun x => Coulomb.pairPotential x * ‖ψ.value s x‖^2) := ψ.pair_integrable s
    rw [integral_add hn hp, integral_neg]
  unfold energy Coulomb.form Coulomb.kinetic Coulomb.nuclearEnergy Coulomb.pairEnergy
  rw [hK]
  simp_rw [hV, Finset.sum_add_distrib,Finset.sum_neg_distrib]
  unfold Coulomb.nuclearPotential Coulomb.pairPotential
  ring

lemma asH1_energy {n : ℕ} (Z : ℕ) (hZ : 1 ≤ Z) {ψ : Wavefunction n} {g : Gradient n}
    (hw : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hg : ∀ σ i a, MemLp (g σ i a) 2 volume) :
    Coulomb.form (Coulomb.atom Z hZ) (asH1 ψ g hw hψ hg) = energy Z ψ g := by
  exact (fromH1_energy Z hZ (asH1 ψ g hw hψ hg)).symm

end NeutralAtom

end

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_CorePointMeasurable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb

lemma ae_position_ne (n : ℕ) (y : Space) : ∀ᵐ x : Configuration n,∀ i,position x i≠y := by
  rw [ae_all_iff]
  intro i
  let L : Configuration n →ₗ[ℝ] ℝ :=
    { toFun := fun x => x (i,0)
      map_add' := by intro x z; rfl
      map_smul' := by intro c x; rfl }
  have hL : LinearMap.ker L≠⊤ := by
    intro h
    have hh : EuclideanSpace.single (i,0) (1:ℝ)∈LinearMap.ker L := by rw [h]; trivial
    change (EuclideanSpace.single (i,0) (1:ℝ)) (i,0)=0 at hh
    simp at hh
  let v : Configuration n := EuclideanSpace.single (i,0) (y 0)
  have hv : v (i,0)=y 0 := by simp [v]
  have hz := Measure.addHaar_submodule (volume : Measure (Configuration n)) (LinearMap.ker L) hL
  have hnull : (volume : Measure (Configuration n)) {x | position x i=y}=0 := by
    apply measure_mono_null (t := (fun x : Configuration n => x+(-v)) ⁻¹' (LinearMap.ker L : Set (Configuration n)))
    · intro x hx
      change (x+(-v)) (i,0)=0
      simp only [PiLp.add_apply,PiLp.neg_apply,hv]
      have hs := congrArg (fun z : Space => z 0) hx
      change x (i,0)=y 0 at hs
      rw [hs,add_neg_cancel]
    · rw [measure_preimage_add_right,hz]
  rw [ae_iff]
  simpa only [not_not] using hnull

end Coulomb

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_RegularizedBounds
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators ContDiff
noncomputable section
namespace NeutralAtom
lemma radial_rpow_partial {l:ℝ} (hl:l≠0) (p:ℝ) (x:Position) (b:Fin 3) :
    dirPartial (fun y:Position => (‖y‖^2+l^2)^p) (axis b) x =
      p*(‖x‖^2+l^2)^(p-1)*(2*x b) := by
  have hq:0<‖x‖^2+l^2:=add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)
  have H:=((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (l^2)).rpow_const (p:=p) (Or.inl hq.ne')
  unfold dirPartial
  rw [H.fderiv]
  simp [axis,EuclideanSpace.inner_single_right,mul_assoc]
lemma regularized_second_partial {l:ℝ} (hl:l≠0) (x:Position) (a b:Fin 3) :
    dirPartial (dirPartial (regularizedKernel l) (axis a)) (axis b) x=
      -(if a=b then (1:ℝ) else 0)*(‖x‖^2+l^2)^(-3/2:ℝ)+
        3*x a*x b*(‖x‖^2+l^2)^(-5/2:ℝ) := by
  have he:dirPartial (regularizedKernel l) (axis a)=fun x => -x a*(‖x‖^2+l^2)^(-3/2:ℝ):=
    funext fun x => dirPartial_regularizedKernel hl a x
  rw [he]
  have hcoord := ((EuclideanSpace.proj (𝕜:=ℝ) a).hasFDerivAt (x:=x)).neg
  change HasFDerivAt (fun y:Position => -y a) _ x at hcoord
  have hd: DifferentiableAt ℝ (fun y:Position => (‖y‖^2+l^2)^(-3/2:ℝ)) x := by
    exact (((hasStrictFDerivAt_norm_sq x).hasFDerivAt.add_const (l^2)).rpow_const
      (p:=(-3/2:ℝ)) (Or.inl (add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)).ne')).differentiableAt
  rw [dirPartial_mul hcoord.differentiableAt hd,radial_rpow_partial hl]
  have hc:dirPartial (fun y:Position => -y a) (axis b) x= -(if a=b then (1:ℝ) else 0) := by
    unfold dirPartial
    rw [hcoord.fderiv]
    simp [axis,PiLp.single_apply]
  rw [hc]
  norm_num
  ring
lemma regularizedSecond_uniform_bound {l:ℝ} (hl:l≠0) (x:Position) (a b:Fin 3) :
    |dirPartial (dirPartial (regularizedKernel l) (axis a)) (axis b) x|≤4*(l^2)^(-3/2:ℝ) := by
  let q:=‖x‖^2+l^2
  have hq:0<q:=add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hl)
  have hbase:l^2≤q:=by dsimp [q]; nlinarith [sq_nonneg ‖x‖]
  have hab:|x a| * |x b|≤q := by
    have ha:|x a|≤‖x‖:=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x a
    have hb:|x b|≤‖x‖:=by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x b
    have H:=mul_le_mul ha hb (abs_nonneg _) (norm_nonneg x)
    dsimp [q]
    nlinarith [sq_nonneg l]
  have he:q*q^(-5/2:ℝ)=q^(-3/2:ℝ) := by
    rw [mul_comm,←Real.rpow_add_one hq.ne']
    norm_num
  have hb:q^(-3/2:ℝ)≤(l^2)^(-3/2:ℝ):=
    Real.rpow_le_rpow_of_nonpos (sq_pos_of_ne_zero hl) hbase (by norm_num)
  rw [regularized_second_partial hl]
  calc
    _≤|-(if a=b then (1:ℝ) else 0)*q^(-3/2:ℝ)|+|3*x a*x b*q^(-5/2:ℝ)|:=abs_add_le _ _
    _≤q^(-3/2:ℝ)+3*q^(-3/2:ℝ) := by
      apply add_le_add
      · split_ifs <;> simp [abs_of_nonneg (Real.rpow_nonneg hq.le _),Real.rpow_nonneg hq.le]
      · simp only [abs_mul,abs_of_nonneg (Real.rpow_nonneg hq.le _)]
        rw [abs_of_pos (by norm_num : (0:ℝ)<3)]
        rw [show 3* |x a| * |x b|=3*(|x a| * |x b|) by ring, mul_assoc,←he]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hab (Real.rpow_nonneg hq.le _)) (by norm_num)
    _≤_:=by nlinarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_BodyCoefficient
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma oneBody_second_derivative {n:ℕ} (f:Space → ℝ) (hf:ContDiff ℝ ∞ f)
    (i j k:Fin n) (a b:Fin 3) (x:Configuration n) :
    fderiv ℝ (fun y => fderiv ℝ (fun z => f (position z i)) y (EuclideanSpace.single (j,a) 1))
      x (EuclideanSpace.single (k,b) 1)=
      if i=j ∧ i=k then fderiv ℝ (fun y => fderiv ℝ f y (EuclideanSpace.single a 1))
        (position x i) (EuclideanSpace.single b 1) else 0 := by
  have hd:ContDiff ℝ ∞ (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)):=
    (hf.fderiv_right (by simp)).clm_apply contDiff_const
  simp_rw [oneBody_derivative f hf]
  by_cases hj:i=j
  · simp only [hj,ite_true,true_and]
    exact oneBody_derivative _ hd j k b x
  · simp [hj]
lemma rootReciprocalCoefficient_sq (l e:ℝ) (hl:l≠0) (he:0<e) (x:Space):
    ((rootReciprocalCoefficient l e hl he).value x)^2=(reciprocalCoefficient l e hl he).value x := by
  change ((regularizedU l e x)^(-1/2:ℝ))^2=(regularizedU l e x)⁻¹
  rw [←Real.rpow_two,←Real.rpow_mul (regularizedU_pos he x).le]
  norm_num [Real.rpow_neg_one]

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_PotentialAddRsmul
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.Coulomb.packetIndexCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Set
open scoped BigOperators ENNReal Classical NNReal ComplexConjugate
namespace Coulomb
open ContinuousLinearMap
open scoped Convolution

lemma potential_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ)
    (s : Spins n) (V : Configuration n → ℝ)
    (hψ : Integrable (fun x => V x * ‖ψ.value s x‖^2))
    (hφ : Integrable (fun x => V x * ‖φ.value s x‖^2))
    (hadd : Integrable (fun x => V x * ‖(ψ.add φ).value s x‖^2)) :
    (∫ x, V x * ‖(ψ.add (φ.rsmul t)).value s x‖^2) =
      (1-t)*(∫ x, V x * ‖ψ.value s x‖^2) +
      (t^2-t)*(∫ x, V x * ‖φ.value s x‖^2) +
      t*(∫ x, V x * ‖(ψ.add φ).value s x‖^2) := by
  have heq : ∀ x, V x * ‖(ψ.add (φ.rsmul t)).value s x‖^2 =
      (1-t)*(V x*‖ψ.value s x‖^2) + (t^2-t)*(V x*‖φ.value s x‖^2) +
      t*(V x*‖(ψ.add φ).value s x‖^2) := by
    intro x
    change V x * ‖ψ.value s x + (t : ℂ)*φ.value s x‖^2 = _
    rw [norm_add_rsmul_sq]
    change _ = (1-t)*(V x*‖ψ.value s x‖^2) + (t^2-t)*(V x*‖φ.value s x‖^2) +
      t*(V x*‖ψ.value s x + φ.value s x‖^2)
    ring
  simp_rw [heq]
  have hsum : Integrable (fun x => (1-t)*(V x*‖ψ.value s x‖^2) +
      (t^2-t)*(V x*‖φ.value s x‖^2)) := (hψ.const_mul _).add (hφ.const_mul _)
  rw [integral_add hsum (hadd.const_mul t),
    integral_add (hψ.const_mul (1-t)) (hφ.const_mul (t^2-t))]
  simp only [integral_const_mul]

lemma nuclearEnergy_add_rsmul {M n : ℕ} (S : Nuclei M) (ψ φ : H1Vector n) (t : ℝ) :
    nuclearEnergy S (ψ.add (φ.rsmul t)) =
      (1-t)*nuclearEnergy S ψ + (t^2-t)*nuclearEnergy S φ +
      t*nuclearEnergy S (ψ.add φ) := by
  unfold nuclearEnergy
  simp_rw [potential_add_rsmul ψ φ t _ _ (ψ.nuclear_integrable S _)
    (φ.nuclear_integrable S _) ((ψ.add φ).nuclear_integrable S _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma pairEnergy_add_rsmul {n : ℕ} (ψ φ : H1Vector n) (t : ℝ) :
    pairEnergy (ψ.add (φ.rsmul t)) =
      (1-t)*pairEnergy ψ + (t^2-t)*pairEnergy φ + t*pairEnergy (ψ.add φ) := by
  unfold pairEnergy
  simp_rw [potential_add_rsmul ψ φ t _ _ (ψ.pair_integrable _)
    (φ.pair_integrable _) ((ψ.add φ).pair_integrable _)]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

lemma form_add_rsmul {M n : ℕ} (S : Nuclei M) (ψ φ : H1Vector n) (t : ℝ) :
    form S (ψ.add (φ.rsmul t)) =
      (1-t)*form S ψ + (t^2-t)*form S φ + t*form S (ψ.add φ) := by
  rw [form, kinetic_add_rsmul, nuclearEnergy_add_rsmul, pairEnergy_add_rsmul]
  unfold form
  ring

open scoped Topology

lemma linear_term_zero_of_eventually_quadratic_nonneg (A B : ℝ)
    (h : ∀ᶠ t : ℝ in 𝓝 0, 0 ≤ A*t+B*t^2) : A = 0 := by
  have hc : ContinuousAt (fun t : ℝ => A+B*t) 0 := by fun_prop
  have hp : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 ≤ A+B*t := by
    filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht hpos
    have hpos' : 0 < t := hpos
    have heq : A*t+B*t^2 = (A+B*t)*t := by ring
    rw [heq] at ht
    exact nonneg_of_mul_nonneg_left ht hpos'
  have hm : ∀ᶠ t : ℝ in 𝓝[<] 0, A+B*t ≤ 0 := by
    filter_upwards [h.filter_mono inf_le_left, self_mem_nhdsWithin] with t ht hneg
    have hneg' : t < 0 := hneg
    have heq : A*t+B*t^2 = (- (A+B*t))*(-t) := by ring
    rw [heq] at ht
    have hu := nonneg_of_mul_nonneg_left ht (neg_pos.mpr hneg')
    linarith
  have htp : Filter.Tendsto (fun t : ℝ => A+B*t) (𝓝[>] (0 : ℝ)) (𝓝 (A+B*0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have htm : Filter.Tendsto (fun t : ℝ => A+B*t) (𝓝[<] (0 : ℝ)) (𝓝 (A+B*0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  have hge := ge_of_tendsto htp hp
  have hle := le_of_tendsto htm hm
  simp only [mul_zero, add_zero] at hge hle
  exact le_antisymm hle hge

end Coulomb

end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakSchwartzDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

private lemma compact_mul_memLp_integrable (f:E → ℂ) (hf:Continuous f)
    (hc:HasCompactSupport f) (u:E → ℂ) (hu:MemLp u 2 volume) :
    Integrable (fun x => f x*u x) :=
  (hf.memLp_of_hasCompactSupport hc (p:=2)).integrable_mul hu
private lemma compact_complex_integral_decompose (f:E → ℂ) (hf:Continuous f)
    (hc:HasCompactSupport f) (u:E → ℂ) (hu:MemLp u 2 volume) :
    (∫ x,f x*u x)=(∫ x,((f x).re:ℂ)*u x)+Complex.I*(∫ x,((f x).im:ℂ)*u x) := by
  have hr := compact_mul_memLp_integrable _
    (Complex.continuous_ofReal.comp (Complex.continuous_re.comp hf))
    (hc.comp_left (g:= fun z:ℂ => (z.re:ℂ)) (by simp)) u hu
  have hi := compact_mul_memLp_integrable _
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp hf))
    (hc.comp_left (g:= fun z:ℂ => (z.im:ℂ)) (by simp)) u hu
  have he (x:E) : f x*u x=((f x).re:ℂ)*u x+Complex.I*(((f x).im:ℂ)*u x) := by
    conv_lhs => rw [←(f x).re_add_im]
    ring
  simp_rw [he]
  change Integrable (fun x => ((f x).re:ℂ)*u x) at hr
  change Integrable (fun x => ((f x).im:ℂ)*u x) at hi
  rw [integral_add hr (hi.const_mul _),integral_const_mul]

lemma weak_directional_complex_test {u d : E → ℂ} (hu : MemLp u 2 volume)
    (hd : MemLp d 2 volume) (a : E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x))
    (φ : E → ℂ) (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x,fderiv ℝ φ x a*u x)=-(∫ x,φ x*d x) := by
  have hr := hw (fun x => (φ x).re) (Complex.reCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hi := hw (fun x => (φ x).im) (Complex.imCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hdr (x:E) : fderiv ℝ (fun y => (φ y).re) x a=(fderiv ℝ φ x a).re := by
    exact congrArg (fun L:E →L[ℝ] ℝ => L a) ((Complex.reCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hdi (x:E) : fderiv ℝ (fun y => (φ y).im) x a=(fderiv ℝ φ x a).im := by
    exact congrArg (fun L:E →L[ℝ] ℝ => L a) ((Complex.imCLM.hasFDerivAt.comp x ((hφ.differentiable (by simp)) x).hasFDerivAt).fderiv)
  have hD : Continuous (fun x => fderiv ℝ φ x a) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [compact_complex_integral_decompose _ hD (hc.fderiv_apply ℝ a) u hu,
    compact_complex_integral_decompose _ hφ.continuous hc d hd]
  simp only [hdr] at hr
  simp only [hdi] at hi
  rw [hr,hi]
  ring

section
omit [MeasurableSpace E] [BorelSpace E]

private lemma weakCut_smooth (k:ℕ) : ContDiff ℝ ∞ (weakCut (E:=E) k) :=
  (weakCutBump (E:=E)).contDiff.comp (contDiff_const.smul contDiff_id)
private lemma weakCut_compact (k:ℕ) : HasCompactSupport (weakCut (E:=E) k) := by
  exact (weakCutBump (E:=E)).hasCompactSupport.comp_homeomorph
    (Homeomorph.smul (Units.mk0 (((k:ℝ)+1)⁻¹) (by positivity)))
private lemma weakCut_fderiv (k:ℕ) (x a:E) :
    fderiv ℝ (weakCut k) x a=((k:ℝ)+1)⁻¹*fderiv ℝ (weakCutBump (E:=E)) (((k:ℝ)+1)⁻¹ • x) a := by
  have h := (((weakCutBump (E:=E)).contDiff (n:=⊤)).differentiable (by simp) _).hasFDerivAt.comp x
    ((hasFDerivAt_id (𝕜:=ℝ) x).const_smul (((k:ℝ)+1)⁻¹))
  have HH := congrArg (fun L:E →L[ℝ] ℝ => L a) h.fderiv
  unfold weakCut
  simpa only [Function.comp_def,Pi.smul_apply,id_eq,ContinuousLinearMap.comp_apply,smul_apply,ContinuousLinearMap.id_apply,map_smul,smul_eq_mul] using HH
private lemma weakCut_bound : ∃ C:ℝ,0 ≤ C ∧ ∀ k x a,
    |fderiv ℝ (weakCut (E:=E) k) x a| ≤ ((k:ℝ)+1)⁻¹*C*‖a‖ := by
  obtain ⟨C,hC⟩ := (((weakCutBump (E:=E)).contDiff (n:=⊤)).continuous_fderiv (by simp)).bounded_above_of_compact_support
    ((weakCutBump (E:=E)).hasCompactSupport.fderiv ℝ)
  refine ⟨C,(norm_nonneg _).trans (hC 0),?_⟩
  intro k x a
  rw [weakCut_fderiv,abs_mul,abs_of_pos (by positivity : (0:ℝ)<((k:ℝ)+1)⁻¹)]
  calc
    _ ≤ ((k:ℝ)+1)⁻¹*(C*‖a‖) := mul_le_mul_of_nonneg_left
      (((fderiv ℝ (weakCutBump (E:=E)) _).le_opNorm a).trans (mul_le_mul_of_nonneg_right (hC _) (norm_nonneg _))) (by positivity)
    _ = _ := by ring
private lemma weakCut_tendsto (x:E) : Tendsto (fun k => weakCut k x) atTop (𝓝 1) := by
  have ht : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹ • x) atTop (𝓝 (0:E)) := by
    have hi : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 (0:ℝ)) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
    simpa using hi.smul_const x
  have H := ((weakCutBump (E:=E)).continuous.tendsto (0:E)).comp ht
  have h1 : (weakCutBump (E:=E)) (0:E)=1 :=
    (weakCutBump (E:=E)).one_of_mem_closedBall (by simp [weakCutBump])
  simpa only [weakCut,Function.comp_def,h1] using H

end

lemma weak_directional_schwartz_test {u d : E → ℂ} (hu : MemLp u 2 volume)
    (hd : MemLp d 2 volume) (a : E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x))
    (Φ : 𝓢(E,ℂ)) :
    (∫ x,(∂_{a} Φ) x*u x)=-(∫ x,Φ x*d x) := by
  obtain ⟨C,hC,hb⟩ := weakCut_bound (E:=E)
  have hinv (k:ℕ) : ((k:ℝ)+1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α:=ℝ) k; linarith)
  have hi0 : Tendsto (fun k:ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have hdt (x:E) : Tendsto (fun k => fderiv ℝ (weakCut k) x a) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun k => hb k x a)
    simpa using (hi0.mul_const C).mul_const ‖a‖
  have hc0 (k:ℕ) (x:E) : 0 ≤ weakCut k x := (weakCutBump (E:=E)).nonneg
  have hc1 (k:ℕ) (x:E) : weakCut k x ≤ 1 := (weakCutBump (E:=E)).le_one
  let F : ℕ → E → ℂ := fun k x =>
    ((fderiv ℝ (weakCut k) x a:ℂ)*Φ x+(weakCut k x:ℂ)*(∂_{a} Φ) x)*u x
  let G : ℕ → E → ℂ := fun k x => (weakCut k x:ℂ)*Φ x*d x
  have he (k:ℕ) : (∫ x,F k x)=-(∫ x,G k x) := by
    let φ : E → ℂ := fun x => (weakCut k x:ℂ)*Φ x
    have hφ : ContDiff ℝ ∞ φ :=
      (Complex.ofRealCLM.contDiff.comp (weakCut_smooth k)).mul (Φ.smooth ⊤)
    have hf (x:E) : fderiv ℝ φ x a =
        (fderiv ℝ (weakCut k) x a:ℂ)*Φ x+(weakCut k x:ℂ)*(∂_{a} Φ) x := by
      have H := (((Complex.ofRealCLM.hasFDerivAt.comp x
        ((weakCut_smooth k).differentiable (by simp) x).hasFDerivAt)).mul (Φ.hasFDerivAt x)).fderiv
      have HH := congrArg (fun L:E →L[ℝ] ℂ => L a) H
      have HH2 : fderiv ℝ φ x a = (weakCut k x:ℂ)*fderiv ℝ Φ x a+Φ x*(fderiv ℝ (weakCut k) x a:ℂ) := by
        simpa only [φ,Pi.mul_def,Pi.mul_apply,Function.comp_def,add_apply,smul_apply,ContinuousLinearMap.comp_apply,Complex.ofRealCLM_apply,smul_eq_mul] using HH
      rw [SchwartzMap.lineDerivOp_apply_eq_fderiv,HH2]
      ring
    have H := weak_directional_complex_test hu hd a hw φ hφ
      (((weakCut_compact k).comp_left (by simp : ((0:ℝ):ℂ)=0)).mul_right)
    simpa only [hf,φ,F,G] using H
  have hφu : Integrable (fun x => ‖Φ x‖*‖u x‖) :=
    ((Φ.memLp 2 volume).norm).integrable_mul hu.norm
  have hdu : Integrable (fun x => ‖(∂_{a} Φ) x‖*‖u x‖) :=
    (((∂_{a} Φ).memLp 2 volume).norm).integrable_mul hu.norm
  have hφd : Integrable (fun x => ‖Φ x‖*‖d x‖) :=
    ((Φ.memLp 2 volume).norm).integrable_mul hd.norm
  have hFm (k:ℕ) : AEStronglyMeasurable (F k) volume := by
    exact (((Complex.continuous_ofReal.comp
      (((weakCut_smooth k).continuous_fderiv (by simp)).clm_apply (continuous_const (y:=a)))).mul Φ.continuous).add
      ((Complex.continuous_ofReal.comp (weakCut_smooth k).continuous).mul
        (∂_{a} Φ).continuous)).aestronglyMeasurable.mul hu.aestronglyMeasurable
  have hF : Tendsto (fun k => ∫ x,F k x) atTop (𝓝 (∫ x,(∂_{a} Φ) x*u x)) := by
    apply tendsto_integral_of_dominated_convergence
      (fun x => C*‖a‖*(‖Φ x‖*‖u x‖)+‖(∂_{a} Φ) x‖*‖u x‖)
      hFm ((hφu.const_mul _).add hdu)
    · intro k
      filter_upwards [] with x
      dsimp [F]
      rw [norm_mul]
      have H1 : ‖(fderiv ℝ (weakCut k) x a:ℂ)‖ ≤ C*‖a‖ := by
        rw [Complex.norm_real,Real.norm_eq_abs]
        exact (hb k x a).trans (by nlinarith [mul_nonneg hC (norm_nonneg a),hinv k])
      have H2 : ‖(weakCut k x:ℂ)‖ ≤ 1 := by
        simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc0 k x)] using hc1 k x
      calc
        _ ≤ (‖(fderiv ℝ (weakCut k) x a:ℂ)‖*‖Φ x‖+
          ‖(weakCut k x:ℂ)‖*‖(∂_{a} Φ) x‖)*‖u x‖ := by
          have HH := norm_add_le ((fderiv ℝ (weakCut k) x a:ℂ)*Φ x) ((weakCut k x:ℂ)*(∂_{a} Φ) x)
          simpa only [norm_mul] using mul_le_mul_of_nonneg_right HH (norm_nonneg (u x))
        _ ≤ (C*‖a‖*‖Φ x‖+1*‖(∂_{a} Φ) x‖)*‖u x‖ :=
          mul_le_mul_of_nonneg_right (add_le_add (mul_le_mul_of_nonneg_right H1 (norm_nonneg _))
            (mul_le_mul_of_nonneg_right H2 (norm_nonneg _))) (norm_nonneg _)
        _ = _ := by ring
    · filter_upwards [] with x
      have H := (((Complex.continuous_ofReal.tendsto 0).comp (hdt x)).mul_const (Φ x)).add
        (((Complex.continuous_ofReal.tendsto 1).comp (weakCut_tendsto x)).mul_const ((∂_{a} Φ) x))
      simpa only [F,Complex.ofReal_zero,zero_mul,Complex.ofReal_one,one_mul,zero_add,Function.comp_apply] using H.mul_const (u x)
  have hG : Tendsto (fun k => ∫ x,G k x) atTop (𝓝 (∫ x,Φ x*d x)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => ‖Φ x‖*‖d x‖)
      (fun k => (((Complex.continuous_ofReal.comp (weakCut_smooth k).continuous).mul
        Φ.continuous).aestronglyMeasurable.mul hd.aestronglyMeasurable)) hφd
    · intro k
      filter_upwards [] with x
      dsimp [G]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hc0 k x)]
      nlinarith [hc1 k x,norm_nonneg (Φ x),norm_nonneg (d x),mul_nonneg (norm_nonneg (Φ x)) (norm_nonneg (d x))]
    · filter_upwards [] with x
      simpa only [G,Complex.ofReal_one,one_mul,Function.comp_apply,Pi.mul_apply] using
        (((Complex.continuous_ofReal.tendsto 1).comp (weakCut_tendsto x)).mul_const (Φ x)).mul_const (d x)
  exact tendsto_nhds_unique hF (by simpa only [he] using hG.neg)

lemma l2_weakDeriv_tempered {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    ∂_{a} (u:𝓢'(E,ℂ))=(d:𝓢'(E,ℂ)) := by
  ext Φ
  simp only [TemperedDistribution.lineDerivOp_apply_apply,map_neg,Lp.toTemperedDistribution_apply,smul_eq_mul]
  have H := weak_directional_schwartz_test (Lp.memLp u) (Lp.memLp d) a hw Φ
  simpa only [neg_neg] using congrArg Neg.neg H
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_WeakFourierDerivative
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped BigOperators ENNReal NNReal Topology SchwartzMap LineDeriv FourierTransform ComplexConjugate ContDiff
noncomputable section
namespace Coulomb
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma l2_weakDeriv_fourier {u d : Lp ℂ 2 (volume:Measure E)} (a:E)
    (hw : ∀ φ : E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*d x)) :
    (𝓕 d : Lp ℂ 2 (volume:Measure E)) =ᵐ[volume]
      fun ξ => (2*Real.pi*Complex.I)*(inner ℝ ξ a:ℂ)*(𝓕 u : Lp ℂ 2 (volume:Measure E)) ξ := by
  have H := congrArg (fun T:𝓢'(E,ℂ) => 𝓕 T) (l2_weakDeriv_tempered a hw)
  rw [TemperedDistribution.fourier_lineDerivOp_eq,Lp.fourier_toTemperedDistribution_eq,
    Lp.fourier_toTemperedDistribution_eq] at H
  have hg : Continuous (fun ξ:E => (2*Real.pi*Complex.I)*(inner ℝ ξ a:ℂ)) := by fun_prop
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp (𝓕 d : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num))
    (((Lp.memLp (𝓕 u : Lp ℂ 2 (volume:Measure E))).locallyIntegrable (by norm_num)).continuous_mul hg)
  intro φ hφ hc
  let χ : E → ℂ := fun x => (φ x:ℂ)
  have hχ : ContDiff ℝ ∞ χ := Complex.ofRealCLM.contDiff.comp hφ
  have hχc : HasCompactSupport χ := hc.comp_left (g:=fun r:ℝ => (r:ℂ)) (by simp)
  let Φ : 𝓢(E,ℂ) := hχc.toSchwartzMap hχ
  have ht : (fun ξ:E => (inner ℝ ξ a:ℂ)).HasTemperateGrowth := by fun_prop
  have HH := congrArg (fun T:𝓢'(E,ℂ) => T Φ) H
  simp only [smul_apply,smul_eq_mul,
    TemperedDistribution.smulLeftCLM_apply_apply,Lp.toTemperedDistribution_apply] at HH
  change (2*Real.pi*Complex.I)*(∫ x,
    (SchwartzMap.smulLeftCLM ℂ (fun ξ:E => (inner ℝ ξ a:ℂ)) Φ) x * (𝓕 u : Lp ℂ 2 (volume:Measure E)) x)=
      ∫ x,Φ x*(𝓕 d : Lp ℂ 2 (volume:Measure E)) x at HH
  rw [←integral_const_mul] at HH
  calc
    _=∫ x,Φ x*(𝓕 d : Lp ℂ 2 (volume:Measure E)) x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Φ,χ,HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
    _= _ := HH.symm
    _= _ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [SchwartzMap.smulLeftCLM_apply ht,smul_eq_mul,Φ,χ,
        HasCompactSupport.toSchwartzMap_toFun,Complex.real_smul]
      ring

end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_H1VectorL2
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology ComplexConjugate ContDiff BigOperators
noncomputable section
namespace Coulomb
namespace H1Vector
variable {n:ℕ}
lemma gradientL2_ae (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    (u.gradientL2 s a:Configuration n → ℂ)=ᵐ[volume]u.gradient s a :=
  (u.partial_L2 s a).coeFn_toLp
lemma weak_partial_L2 (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3)
    (φ:Configuration n → ℝ) (hφ:ContDiff ℝ ∞ φ) (hc:HasCompactSupport φ) :
    (∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*u.valueL2 s x)=
      -(∫ x,(φ x:ℂ)*u.gradientL2 s a x) := by
  have h1:(∫ x,(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ)*u.valueL2 s x)=
      ∫ x,u.value s x*(fderiv ℝ φ x (EuclideanSpace.single a 1):ℂ) := by
    apply integral_congr_ae
    filter_upwards [u.valueL2_ae s] with x hx
    rw [hx,mul_comm]
  have h2:(∫ x,(φ x:ℂ)*u.gradientL2 s a x)=∫ x,u.gradient s a x*(φ x:ℂ) := by
    apply integral_congr_ae
    filter_upwards [u.gradientL2_ae s a] with x hx
    rw [hx,mul_comm]
  rw [h1,h2]
  exact u.weak_partial s a φ hφ hc

end H1Vector

end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology FourierTransform ComplexConjugate BigOperators ContDiff
noncomputable section
namespace Coulomb
lemma memlp_real_inner_integrable {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g:X → ℂ} (hf:MemLp f 2 μ) (hg:MemLp g 2 μ) : Integrable (fun x => inner ℝ (f x) (g x)) μ := by
  apply (hf.norm.integrable_sq.add hg.norm.integrable_sq).mono'
    (hf.aestronglyMeasurable.inner hg.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    have hb:=norm_inner_le_norm (𝕜:=ℝ) (f x) (g x)
    have hs:=sq_nonneg (‖f x‖-‖g x‖)
    change ‖inner ℝ (f x) (g x)‖ ≤ ‖f x‖^2+‖g x‖^2
    nlinarith [sq_nonneg ‖f x‖,sq_nonneg ‖g x‖]
lemma l2_weakDeriv_skew {E:Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {u du v dv:Lp ℂ 2 (volume:Measure E)} (a:E)
    (hu:∀ φ:E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*u x)=-(∫ x,(φ x:ℂ)*du x))
    (hv:∀ φ:E → ℝ,ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x,(fderiv ℝ φ x a:ℂ)*v x)=-(∫ x,(φ x:ℂ)*dv x)) :
    inner ℂ du v= -inner ℂ u dv := by
  rw [←(Lp.fourierTransformₗᵢ E ℂ).inner_map_map du v,
    ←(Lp.fourierTransformₗᵢ E ℂ).inner_map_map u dv,L2.inner_def,L2.inner_def,←integral_neg]
  apply integral_congr_ae
  filter_upwards [l2_weakDeriv_fourier a hu,l2_weakDeriv_fourier a hv] with ξ h1 h2
  change inner ℂ ((𝓕 du:Lp ℂ 2 (volume:Measure E)) ξ) ((𝓕 v:Lp ℂ 2 (volume:Measure E)) ξ)=
    -inner ℂ ((𝓕 u:Lp ℂ 2 (volume:Measure E)) ξ) ((𝓕 dv:Lp ℂ 2 (volume:Measure E)) ξ)
  rw [h1,h2]
  simp only [RCLike.inner_apply,map_mul,map_ofNat,Complex.conj_ofReal,Complex.conj_I]
  ring

lemma h1_green {n:ℕ} (u v:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    (∫ x,inner ℝ (u.gradient s a x) (v.value s x)) =
      -(∫ x,inner ℝ (u.value s x) (v.gradient s a x)) := by
  have H:=l2_weakDeriv_skew (EuclideanSpace.single a (1:ℝ)) (u.weak_partial_L2 s a) (v.weak_partial_L2 s a)
  have HH:=congrArg Complex.re H
  rw [L2.inner_def,L2.inner_def,Complex.neg_re] at HH
  change RCLike.re (∫ x,inner ℂ (u.gradientL2 s a x) (v.valueL2 s x))=
    -RCLike.re (∫ x,inner ℂ (u.valueL2 s x) (v.gradientL2 s a x)) at HH
  rw [←integral_re (L2.integrable_inner (u.gradientL2 s a) (v.valueL2 s)),
    ←integral_re (L2.integrable_inner (u.valueL2 s) (v.gradientL2 s a))] at HH
  convert HH using 1
  · apply integral_congr_ae
    filter_upwards [u.gradientL2_ae s a,v.valueL2_ae s] with x hx hy
    rw [hx,hy]
    rfl
  · congr 1
    apply integral_congr_ae
    filter_upwards [u.valueL2_ae s,v.gradientL2_ae s a] with x hx hy
    rw [hx,hy]
    rfl

lemma h1_multiplier_ibp {n:ℕ} (u:H1Vector n) (s:Spins n) (a:Fin n × Fin 3)
    (F:Configuration n → ℝ) (hF:ContDiff ℝ ∞ F) (B D:ℝ)
    (hB:∀ x,|F x|≤B) (hD:∀ b x,|fderiv ℝ F x (EuclideanSpace.single b 1)|≤D) :
    (∫ x,fderiv ℝ F x (EuclideanSpace.single a 1)*‖u.value s x‖^2)=
      -2*(∫ x,F x*inner ℝ (u.value s x) (u.gradient s a x)) := by
  let v:=u.smoothMul F hF B D hB hD
  have H:=h1_green u v s a
  have hcross:Integrable (fun x => F x*inner ℝ (u.value s x) (u.gradient s a x)) := by
    have h:Integrable (fun x => inner ℝ ((F x:ℂ)*u.value s x) (u.gradient s a x)) :=
      memlp_real_inner_integrable (v.value_L2 s) (u.partial_L2 s a)
    simpa only [←Complex.real_smul,real_inner_smul_left] using h
  have hder:Integrable (fun x => fderiv ℝ F x (EuclideanSpace.single a 1)*‖u.value s x‖^2) := by
    have h:= memlp_real_inner_integrable (u.value_L2 s)
      (memLp_two_real_mul (u.value_L2 s) ((hF.continuous_fderiv (by simp)).clm_apply continuous_const) (hD a))
    simpa only [←Complex.real_smul,real_inner_smul_right,real_inner_self_eq_norm_sq] using h
  have hl:(∫ x,inner ℝ (u.gradient s a x) (v.value s x))=
      ∫ x,F x*inner ℝ (u.value s x) (u.gradient s a x) := by
    apply integral_congr_ae
    filter_upwards [] with x
    change inner ℝ (u.gradient s a x) ((F x:ℂ)*u.value s x)=_
    rw [←Complex.real_smul,real_inner_smul_right,real_inner_comm]
  have hr:(∫ x,inner ℝ (u.value s x) (v.gradient s a x))=
      (∫ x,fderiv ℝ F x (EuclideanSpace.single a 1)*‖u.value s x‖^2)+
      ∫ x,F x*inner ℝ (u.value s x) (u.gradient s a x) := by
    change (∫ x,inner ℝ (u.value s x) ((fderiv ℝ F x (EuclideanSpace.single a 1):ℂ)*u.value s x+(F x:ℂ)*u.gradient s a x))=_
    simp only [inner_add_right,←Complex.real_smul,real_inner_smul_right,real_inner_self_eq_norm_sq]
    exact integral_add hder hcross
  rw [hl,hr] at H
  linarith
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_H1Pairing
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma real_inner_norm_algebra (z w:ℂ) :
    2*inner ℝ z w=‖z+w‖^2-‖z‖^2-‖w‖^2 := by
  nlinarith [norm_add_sq_real z w]
lemma weighted_inner_integrable {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g:X → ℂ} {V:X → ℝ}
    (hf:Integrable (fun x => V x*‖f x‖^2) μ)
    (hg:Integrable (fun x => V x*‖g x‖^2) μ)
    (ha:Integrable (fun x => V x*‖f x+g x‖^2) μ) :
    Integrable (fun x => V x*inner ℝ (f x) (g x)) μ := by
  convert ((ha.sub hf).sub hg).div_const 2 using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  dsimp only [Pi.sub_apply]
  nlinarith [congrArg (fun t:ℝ => V x*t) (real_inner_norm_algebra (f x) (g x))]
lemma integral_weighted_inner {X:Type*} [MeasurableSpace X] {μ:Measure X}
    {f g:X → ℂ} {V:X → ℝ}
    (hf:Integrable (fun x => V x*‖f x‖^2) μ)
    (hg:Integrable (fun x => V x*‖g x‖^2) μ)
    (ha:Integrable (fun x => V x*‖f x+g x‖^2) μ) :
    2*(∫ x,V x*inner ℝ (f x) (g x) ∂μ)=
      (∫ x,V x*‖f x+g x‖^2 ∂μ)-(∫ x,V x*‖f x‖^2 ∂μ)-(∫ x,V x*‖g x‖^2 ∂μ) := by
  rw [←integral_const_mul]
  calc
    _ = ∫ x,(V x*‖f x+g x‖^2-V x*‖f x‖^2)-V x*‖g x‖^2 ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with x
      nlinarith [congrArg (fun t:ℝ => V x*t) (real_inner_norm_algebra (f x) (g x))]
    _ = _ := by
      have H:=integral_sub (ha.sub hf) hg
      simp only [Pi.sub_apply] at H
      rw [H,integral_sub ha hf]

lemma massPair_polarization {n:ℕ} (u v:H1Vector n) :
    2*massPair u v=mass (u.add v)-mass u-mass v := by
  unfold massPair mass
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  simpa only [one_mul,H1Vector.add] using integral_weighted_inner (V:=fun _ => 1)
    (by simpa using (u.value_L2 s).integrable_norm_pow (by norm_num))
    (by simpa using (v.value_L2 s).integrable_norm_pow (by norm_num))
    (by simpa only [one_mul,H1Vector.add] using ((u.add v).value_L2 s).integrable_norm_pow (by norm_num))
lemma kineticPair_polarization {n:ℕ} (u v:H1Vector n) :
    2*kineticPair u v=kinetic (u.add v)-kinetic u-kinetic v := by
  have h(s:Spins n)(a:Fin n × Fin 3) :
      2*(∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x))=
      (∫ x,‖(u.add v).gradient s a x‖^2)-(∫ x,‖u.gradient s a x‖^2)-(∫ x,‖v.gradient s a x‖^2) := by
    simpa only [one_mul,H1Vector.add] using integral_weighted_inner (V:=fun _ => 1)
      (by simpa using (u.partial_L2 s a).integrable_norm_pow (by norm_num))
      (by simpa using (v.partial_L2 s a).integrable_norm_pow (by norm_num))
      (by simpa only [one_mul,H1Vector.add] using ((u.add v).partial_L2 s a).integrable_norm_pow (by norm_num))
  have H:=congrArg (fun f:Spins n → (Fin n × Fin 3) → ℝ => ∑ s,∑ a,f s a) (funext fun s => funext fun a => h s a)
  simp only [Finset.sum_sub_distrib,←Finset.mul_sum] at H
  unfold kinetic kineticPair
  linarith
lemma nuclearPair_polarization {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) :
    2*nuclearPair S u v=nuclearEnergy S (u.add v)-nuclearEnergy S u-nuclearEnergy S v := by
  unfold nuclearPair nuclearEnergy
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_weighted_inner (u.nuclear_integrable S s) (v.nuclear_integrable S s) ((u.add v).nuclear_integrable S s)
lemma repulsionPair_polarization {n:ℕ} (u v:H1Vector n) :
    2*repulsionPair u v=pairEnergy (u.add v)-pairEnergy u-pairEnergy v := by
  unfold repulsionPair pairEnergy
  rw [Finset.mul_sum,←Finset.sum_sub_distrib,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro s _
  exact integral_weighted_inner (u.pair_integrable s) (v.pair_integrable s) ((u.add v).pair_integrable s)
lemma formPair_polarization {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) :
    2*formPair S u v=form S (u.add v)-form S u-form S v := by
  unfold formPair form
  linarith [kineticPair_polarization u v,nuclearPair_polarization S u v,repulsionPair_polarization u v]
lemma formPair_kinetic_integrable {n:ℕ} (u v:H1Vector n) (s:Spins n) (a:Fin n × Fin 3) :
    Integrable (fun x => inner ℝ (u.gradient s a x) (v.gradient s a x)) :=
  memlp_real_inner_integrable (u.partial_L2 s a) (v.partial_L2 s a)
lemma formPair_nuclear_integrable {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (s:Spins n) :
    Integrable (fun x => (∑ i,attraction S (position x i))*inner ℝ (u.value s x) (v.value s x)) :=
  weighted_inner_integrable (u.nuclear_integrable S s) (v.nuclear_integrable S s) ((u.add v).nuclear_integrable S s)
lemma formPair_repulsion_integrable {n:ℕ} (u v:H1Vector n) (s:Spins n) :
    Integrable (fun x => pairPotential x*inner ℝ (u.value s x) (v.value s x)) :=
  weighted_inner_integrable (u.pair_integrable s) (v.pair_integrable s) ((u.add v).pair_integrable s)

lemma form_ge_sector_bottom {M n:ℕ} (S:Nuclei M) (u:H1Vector n)
    (ha:Antisymmetric u) (E:ℝ) (hE:(E:EReal) ≤ sectorFormBottom S n) :
    E*mass u ≤ form S u := by
  rw [←form_normalized_weight S u]
  by_cases hz:mass u=0
  · simp [hz]
  · have hp:0 < mass u:=lt_of_le_of_ne (mass_nonneg u) (Ne.symm hz)
    have H:E≤form S u.normalized:=EReal.coe_le_coe_iff.mp (hE.trans (sInf_le
      ⟨u.normalized,ha.normalized,mass_normalized u hp,rfl⟩))
    simpa [mul_comm] using mul_le_mul_of_nonneg_left H hp.le

lemma sector_minimizer_weak_eigen (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ}
    (u:H1Vector n) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n)
    (v:H1Vector n) (hv:Antisymmetric v) :
    formPair (atom Z hZ) u v=form (atom Z hZ) u*massPair u v := by
  let E:=form (atom Z hZ) u
  let A:=form (atom Z hZ) (u.add v)-form (atom Z hZ) u-form (atom Z hZ) v-
    E*(mass (u.add v)-mass u-mass v)
  let B:=form (atom Z hZ) v-E*mass v
  have hpoly:∀ᶠ t:ℝ in 𝓝 0,0 ≤ A*t+B*t^2 := by
    apply Eventually.of_forall
    intro t
    have H:=form_ge_sector_bottom (atom Z hZ) (u.add (v.rsmul t)) (ha.add (hv.rsmul t)) E hmin.le
    rw [mass_add_rsmul,form_add_rsmul,hm] at H
    dsimp [E] at H
    dsimp [A,B,E]
    rw [hm]
    nlinarith only [H]
  have H:=linear_term_zero_of_eventually_quadratic_nonneg A B hpoly
  dsimp [A,E] at H
  rw [←formPair_polarization,←massPair_polarization] at H
  linarith
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma integrable_real_bounded_mul {X:Type*} [TopologicalSpace X] [MeasureSpace X]
    [BorelSpace X] {f F:X → ℝ} (hf:Integrable f) (hF:Continuous F)
    (B:ℝ) (hB:∀ x,|F x|≤B) : Integrable (fun x => F x*f x) :=
  hf.bdd_mul hF.aestronglyMeasurable (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hB x)

lemma reciprocal_kinetic_nonneg {n:ℕ} (u:H1Vector n) (s:Spins n)
    (I:Finset (Fin n × Fin 3)) (U w:Configuration n → ℝ)
    (hU:ContDiff ℝ ∞ U) (hw:ContDiff ℝ ∞ w)
    (BU DU Dw Bw DDU:ℝ)
    (hBU:∀ x,|U x|≤BU) (hDU:∀ a x,|fderiv ℝ U x (EuclideanSpace.single a 1)|≤DU)
    (hBw:∀ x,|w x|≤Bw) (hDw:∀ a x,|fderiv ℝ w x (EuclideanSpace.single a 1)|≤Dw)
    (hDDU:∀ a b x,|fderiv ℝ (fun y => fderiv ℝ U y (EuclideanSpace.single a 1)) x (EuclideanSpace.single b 1)|≤DDU)
    (hpos:∀ x,0≤U x) (hinv:∀ x,U x*w x=1)
    (hlap:∀ x,(∑ a∈I,fderiv ℝ (fun y => fderiv ℝ U y (EuclideanSpace.single a 1)) x (EuclideanSpace.single a 1))≤0) :
    let v:=u.smoothMul w hw Bw Dw hBw hDw
    0≤∑ a∈I,∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x) := by
  dsimp only
  let v:=u.smoothMul w hw Bw Dw hBw hDw
  let z:=v.smoothMul U hU BU DU hBU hDU
  have he:∀ t,u.value t=ᵐ[volume]z.value t := by
    intro t
    exact Eventually.of_forall fun x => by
      change u.value t x=(U x:ℂ)*((w x:ℂ)*u.value t x)
      rw [←mul_assoc,←Complex.ofReal_mul,hinv x]
      simp
  let dU:=fun a (x:Configuration n) => fderiv ℝ U x (EuclideanSpace.single a 1)
  let ddU:=fun a (x:Configuration n) => fderiv ℝ (dU a) x (EuclideanSpace.single a 1)
  have hd(a:Fin n × Fin 3):ContDiff ℝ ∞ (dU a):=
    (hU.fderiv_right (by simp)).clm_apply contDiff_const
  have hi(a:Fin n × Fin 3):Integrable (fun x => U x*‖v.gradient s a x‖^2) :=
    integrable_real_bounded_mul ((v.partial_L2 s a).integrable_norm_pow (by norm_num)) hU.continuous BU hBU
  have hj(a:Fin n × Fin 3):Integrable (fun x => dU a x*inner ℝ (v.value s x) (v.gradient s a x)) :=
    integrable_real_bounded_mul (memlp_real_inner_integrable (v.value_L2 s) (v.partial_L2 s a))
      (hd a).continuous DU (hDU a)
  have hk(a:Fin n × Fin 3):Integrable (fun x => ddU a x*‖v.value s x‖^2) :=
    integrable_real_bounded_mul ((v.value_L2 s).integrable_norm_pow (by norm_num))
      (((hd a).continuous_fderiv (by simp)).clm_apply continuous_const) DDU (hDDU a a)
  have hblock(a:Fin n × Fin 3):
      (∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x))=
      (∫ x,U x*‖v.gradient s a x‖^2)-(1/2:ℝ)*(∫ x,ddU a x*‖v.value s x‖^2) := by
    have H:=h1_multiplier_ibp v s a (dU a) (hd a) DU DDU (hDU a) (hDDU a)
    have H':(∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x))=
        (∫ x,U x*‖v.gradient s a x‖^2)+(∫ x,dU a x*inner ℝ (v.value s x) (v.gradient s a x)) := by
      rw [←integral_add (hi a) (hj a)]
      apply integral_congr_ae
      filter_upwards [u.gradient_congr_ae z he s a] with x hx
      rw [hx]
      change inner ℝ ((dU a x:ℂ)*v.value s x+(U x:ℂ)*v.gradient s a x) (v.gradient s a x)=_
      simp only [inner_add_left,←Complex.real_smul,real_inner_smul_left,real_inner_self_eq_norm_sq]
      ring
    dsimp [ddU] at *
    linarith
  change 0≤∑ a∈I,∫ x,inner ℝ (u.gradient s a x) (v.gradient s a x)
  simp_rw [hblock]
  rw [Finset.sum_sub_distrib,←Finset.mul_sum]
  have hh:0≤∑ a∈I,∫ x,U x*‖v.gradient s a x‖^2 :=
    Finset.sum_nonneg fun a _ => integral_nonneg fun x => mul_nonneg (hpos x) (sq_nonneg _)
  have hneg:(∑ a∈I,∫ x,ddU a x*‖v.value s x‖^2)≤0 := by
    rw [←integral_finsetSum _ (fun a _ => hk a)]
    apply integral_nonpos
    intro x
    dsimp only [Pi.zero_apply]
    rw [←Finset.sum_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (hlap x) (sq_nonneg _)
  linarith
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_RegularizedKinetic
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma regularizedU_second {l:ℝ} (hl:l≠0) (e:ℝ) (a b:Fin 3) (x:Space):
    fderiv ℝ (fun y => fderiv ℝ (regularizedU l e) y (EuclideanSpace.single a 1)) x
      (EuclideanSpace.single b 1)=NeutralAtom.dirPartial
        (NeutralAtom.dirPartial (NeutralAtom.regularizedKernel l) (NeutralAtom.axis a))
        (NeutralAtom.axis b) x := by
  simp_rw [regularizedU_partial hl]
  rfl
lemma regularizedU_second_le {l:ℝ} (hl:l≠0) (e:ℝ) (a b:Fin 3) (x:Space):
    |fderiv ℝ (fun y => fderiv ℝ (regularizedU l e) y (EuclideanSpace.single a 1)) x
      (EuclideanSpace.single b 1)|≤4*(l^2)^(-3/2:ℝ) := by
  rw [regularizedU_second hl]
  exact NeutralAtom.regularizedSecond_uniform_bound hl x a b
lemma regularizedU_lap {l:ℝ} (hl:l≠0) (e:ℝ) (x:Space):
    (∑ a:Fin 3,fderiv ℝ (fun y => fderiv ℝ (regularizedU l e) y (EuclideanSpace.single a 1)) x
      (EuclideanSpace.single a 1))≤0 := by
  simp_rw [regularizedU_second hl]
  rw [←NeutralAtom.coordinateLaplacian_eq_partials
    ((NeutralAtom.contDiff_regularizedKernel hl).of_le (by exact WithTop.coe_le_coe.mpr le_top)).contDiffAt,
    NeutralAtom.laplacian_regularizedKernel hl]
  unfold NeutralAtom.regularizedCharge
  apply neg_nonpos.mpr
  positivity

lemma regularized_weight_kinetic {k:ℕ} (u:H1Vector (1+k)) (s:Spins (1+k))
    (l e:ℝ) (hl:l≠0) (he:0<e):
    let w:=reciprocalCoefficient l e hl he
    let v:=u.smoothMul (fun x => w.value (position x 0)) (w.lift_smooth 0) w.bound w.derivBound
      (fun x => w.value_le (position x 0)) (w.lift_deriv_le 0)
    0≤∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x) := by
  let U:=regularizedUCoefficient l e hl
  let w:=reciprocalCoefficient l e hl he
  have hDD:∀ a b (x:Configuration (1+k)),
      |fderiv ℝ (fun y => fderiv ℝ (fun z => U.value (position z 0)) y (EuclideanSpace.single a 1))
        x (EuclideanSpace.single b 1)|≤4*(l^2)^(-3/2:ℝ) := by
    rintro ⟨j,a⟩ ⟨i,b⟩ x
    rw [oneBody_second_derivative U.value U.smooth]
    split_ifs
    · simpa only [U,regularizedUCoefficient] using regularizedU_second_le hl e a b (position x 0)
    · simp only [abs_zero]
      positivity
  have hLap:∀ x:Configuration (1+k),
      (∑ a∈firstCoordinateBlock k,fderiv ℝ (fun y => fderiv ℝ (fun z => U.value (position z 0)) y
        (EuclideanSpace.single a 1)) x (EuclideanSpace.single a 1))≤0 := by
    intro x
    simp only [firstCoordinateBlock,Finset.sum_map]
    change (∑ a:Fin 3,fderiv ℝ (fun y => fderiv ℝ (fun z => U.value (position z 0)) y
      (EuclideanSpace.single (0,a) 1)) x (EuclideanSpace.single (0,a) 1))≤0
    simp_rw [oneBody_second_derivative U.value U.smooth]
    simp only [and_self,ite_true]
    simpa only [U,regularizedUCoefficient] using regularizedU_lap hl e (position x 0)
  have H:=reciprocal_kinetic_nonneg u s (firstCoordinateBlock k)
    (fun x => U.value (position x 0)) (fun x => w.value (position x 0))
    (U.lift_smooth 0) (w.lift_smooth 0) U.bound U.derivBound w.derivBound w.bound (4*(l^2)^(-3/2:ℝ))
    (fun x => U.value_le (position x 0)) (U.lift_deriv_le 0)
    (fun x => w.value_le (position x 0)) (w.lift_deriv_le 0) hDD
    (fun x => by exact (regularizedU_pos (l:=l) he (position x 0)).le)
    (fun x => by exact mul_inv_cancel₀ (regularizedU_pos (l:=l) he (position x 0)).ne') hLap
  simp only [firstCoordinateBlock,Finset.sum_map] at H
  exact H
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Localization_SmoothMultiplier
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff Classical
noncomputable section
namespace NeutralAtom

theorem memLp_bounded_real_smul {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2 volume) {θ : Configuration n → ℝ} (hθ : Continuous θ)
    (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C) : MemLp (fun x => θ x • f x) 2 volume := by
  obtain ⟨C,hC⟩ := hb
  apply hf.of_le_mul (c := C) (hθ.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  exact Eventually.of_forall fun x => by
    change ‖θ x • f x‖ ≤ C * ‖f x‖
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC x) (norm_nonneg _)

theorem integrable_test_real_smul {n : ℕ} {f : Configuration n → ℂ}
    (hf : MemLp f 2 volume) {φ : Configuration n → ℝ} (hφ : Continuous φ)
    (hc : HasCompactSupport φ) : Integrable (fun x => φ x • f x) := by
  exact (hf.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ hc

theorem IsAntisymmetric.multiply {n : ℕ} {ψ : Wavefunction n}
    (hψ : IsAntisymmetric ψ) {θ : Configuration n → ℝ}
    (hθ : ∀ (p : Equiv.Perm (Fin n)) x, θ (x ∘ p) = θ x) :
    IsAntisymmetric (multiplyWavefunction θ ψ) := by
  intro p σ
  filter_upwards [hψ p σ] with x hx
  simp only [multiplyWavefunction, hθ p x, hx, mul_smul_comm]

theorem HasWeakGradient.multiply {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hgLp : ∀ σ i a, MemLp (g σ i a) 2 volume)
    {θ : Configuration n → ℝ} (hθ : ContDiff ℝ ∞ θ) :
    HasWeakGradient (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) := by
  intro σ i a φ hφ hφc
  let dθ : Configuration n → ℝ := fun x => fderiv ℝ θ x (coordinateDirection i a)
  let dφ : Configuration n → ℝ := fun x => fderiv ℝ φ x (coordinateDirection i a)
  have hdθ : Continuous dθ := (hθ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφ : Continuous dφ := (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdφc : HasCompactSupport dφ := hφc.fderiv_apply ℝ _
  have hi₁ : Integrable (fun x => (θ x*dφ x) • ψ σ x) :=
    integrable_test_real_smul (hψ σ) (hθ.continuous.mul hdφ) hdφc.mul_left
  have hi₂ : Integrable (fun x => (φ x*dθ x) • ψ σ x) :=
    integrable_test_real_smul (hψ σ) (hφ.continuous.mul hdθ) hφc.mul_right
  have hi₃ : Integrable (fun x => (φ x*θ x) • g σ i a x) :=
    integrable_test_real_smul (hgLp σ i a)
    (hφ.continuous.mul hθ.continuous) hφc.mul_right
  have h := hg σ i a (fun x => φ x * θ x) (hφ.mul hθ) hφc.mul_right
  have hder : ∀ x, fderiv ℝ (fun x => φ x * θ x) x (coordinateDirection i a) =
      θ x*dφ x + φ x*dθ x := by
    intro x
    change (fderiv ℝ (φ * θ) x) _ = _
    rw [fderiv_mul (hφ.differentiable (by simp)).differentiableAt
      (hθ.differentiable (by simp)).differentiableAt]
    simp [dθ, dφ, smul_eq_mul, add_comm]
  simp_rw [hder] at h
  change (∫ x, (θ x*dφ x + φ x*dθ x) • ψ σ x) =
    -(∫ x, (φ x*θ x) • g σ i a x) at h
  simp_rw [add_smul] at h
  rw [integral_add hi₁ hi₂] at h
  change (∫ x, dφ x • (θ x • ψ σ x)) =
    -(∫ x, φ x • (dθ x • ψ σ x + θ x • g σ i a x))
  simp_rw [smul_add, smul_smul]
  rw [integral_add hi₂ hi₃]
  simp_rw [mul_comm (dφ _) (θ _)]
  linear_combination h

theorem norm_multiplyWavefunction_sq {n : ℕ} (θ : Configuration n → ℝ)
    (ψ : Wavefunction n) (σ : Spins n) (x : Configuration n) :
    ‖multiplyWavefunction θ ψ σ x‖^2 = θ x^2 * ‖ψ σ x‖^2 := by
  simp [multiplyWavefunction, mul_pow]

theorem integrable_weight_multiply {n : ℕ} {θ : Configuration n → ℝ}
    (hθ : Continuous θ) (hb : ∃ C : ℝ, ∀ x, |θ x| ≤ C)
    (ψ : Wavefunction n) (σ : Spins n) {W : Configuration n → ℝ}
    (hi : Integrable (fun x => W x*‖ψ σ x‖^2)) :
    Integrable (fun x => W x*‖multiplyWavefunction θ ψ σ x‖^2) := by
  obtain ⟨C,hC⟩ := hb
  have hb' : ∀ᵐ x : Configuration n ∂volume, ‖θ x^2‖ ≤ C^2 := by
    exact Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using pow_le_pow_left₀ (abs_nonneg (θ x)) (hC x) 2
  have hh := hi.bdd_mul (hθ.pow 2).aestronglyMeasurable hb'
  convert hh using 1
  all_goals try with_reducible_and_instances rfl
  ext x
  rw [norm_multiplyWavefunction_sq]
  simp only [Pi.pow_apply]
  ring

theorem FormDomain.multiply {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : FormDomain ψ g) {θ : Configuration n → ℝ} (hθ : SmoothMultiplier θ) :
    FormDomain (multiplyWavefunction θ ψ) (multiplyGradient θ ψ g) := by
  refine ⟨hg.1.multiply hθ.symmetric,
    hg.2.1.multiply hg.2.2.1 hg.2.2.2.1 hθ.smooth, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact memLp_bounded_real_smul (hg.2.2.1 σ) hθ.smooth.continuous hθ.bounded
  · intro σ i a
    exact (memLp_bounded_real_smul (hg.2.2.1 σ)
      ((hθ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hθ.derivative_bounded i a)).add
      (memLp_bounded_real_smul (hg.2.2.2.1 σ i a) hθ.smooth.continuous hθ.bounded)
  · intro σ i
    exact integrable_weight_multiply hθ.smooth.continuous hθ.bounded ψ σ (hg.2.2.2.2.1 σ i)
  · intro σ i j hij
    exact integrable_weight_multiply hθ.smooth.continuous hθ.bounded ψ σ
      (hg.2.2.2.2.2 σ i j hij)

theorem SmoothMultiplier.const {n : ℕ} (c : ℝ) :
    SmoothMultiplier (fun _ : Configuration n => c) := by
  refine ⟨contDiff_const, fun _ _ => rfl, ⟨|c|, fun _ => le_rfl⟩, ?_⟩
  intro i a
  exact ⟨0, fun x => by simp⟩

theorem FormDomain.scale {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : FormDomain ψ g) (c : ℝ) :
    FormDomain (scaleWavefunction c ψ) (scaleGradient c g) := by
  have he : multiplyGradient (fun _ => c) ψ g = scaleGradient c g := by
    funext σ i a x
    simp [multiplyGradient, scaleGradient]
  change FormDomain (multiplyWavefunction (fun _ => c) ψ) (scaleGradient c g)
  rw [← he]
  exact hg.multiply (SmoothMultiplier.const c)

theorem normSquared_scale {n : ℕ} (c : ℝ) (ψ : Wavefunction n) :
    normSquared (scaleWavefunction c ψ) = c^2 * normSquared ψ := by
  simp only [normSquared, scaleWavefunction, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    integral_const_mul, Finset.mul_sum]

theorem energy_scale {n : ℕ} (Z : ℕ) (c : ℝ) (ψ : Wavefunction n) (g : Gradient n) :
    energy Z (scaleWavefunction c ψ) (scaleGradient c g) = c^2 * energy Z ψ g := by
  simp only [energy, scaleWavefunction, scaleGradient, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  simp_rw [← mul_assoc, mul_comm (coulombPotential Z _) (c^2), mul_assoc,
    integral_const_mul, ← Finset.mul_sum]
  ring

theorem FormDomain.integrable_potential {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (Z : ℕ) (σ : Spins n) :
    Integrable (fun x : Configuration n => coulombPotential Z x*‖ψ σ x‖^2) := by
  have hn := integrable_finsetSum Finset.univ (fun i _ => hd.2.2.2.2.1 σ i)
  have hp := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum (Finset.univ.filter (fun j : Fin n => i < j))
      (fun j hj => hd.2.2.2.2.2 σ i j (Finset.mem_filter.mp hj).2))
  apply ((hn.const_mul (-(Z:ℝ))).add hp).congr
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, coulombPotential, add_mul, Finset.sum_mul, mul_assoc]

end NeutralAtom
end
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_BindingBump
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

theorem bindingCutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (bindingCutoff n) := by
  exact contDiff_prod fun i _ => bindingBump.contDiff.comp (contDiff_apply ℝ Position i)

theorem bindingCutoff_symmetric (n : ℕ) (p : Equiv.Perm (Fin n))
    (x : Configuration n) : bindingCutoff n (x ∘ p) = bindingCutoff n x := by
  exact Equiv.prod_comp p (fun i => bindingBump (x i))

theorem bindingCutoff_nonneg (n : ℕ) (x : Configuration n) : 0 ≤ bindingCutoff n x :=
  Finset.prod_nonneg fun _ _ => bindingBump.nonneg

theorem bindingCutoff_le_one (n : ℕ) (x : Configuration n) : bindingCutoff n x ≤ 1 := by
  exact Finset.prod_le_one (fun _ _ => bindingBump.nonneg) (fun _ _ => bindingBump.le_one)

theorem bindingCutoff_eq_one {n : ℕ} {x : Configuration n} (hx : ‖x‖ ≤ 1) :
    bindingCutoff n x = 1 := by
  apply Finset.prod_eq_one
  intro i _
  apply bindingBump.one_of_mem_closedBall
  simpa [bindingBump, Metric.mem_closedBall, dist_zero_right] using
    (norm_le_pi_norm x i).trans hx

theorem bindingCutoff_eq_zero {n : ℕ} {x : Configuration n} (hx : 2 < ‖x‖) :
    bindingCutoff n x = 0 := by
  have he : ∃ i : Fin n, 2 < ‖x i‖ := by
    by_contra! h
    exact (not_lt_of_ge ((pi_norm_le_iff_of_nonneg (by norm_num : (0:ℝ) ≤ 2)).mpr h)) hx
  obtain ⟨i, hi⟩ := he
  exact Finset.prod_eq_zero (Finset.mem_univ i)
    (bindingBump.zero_of_le_dist (by simpa [bindingBump] using hi.le))

theorem bindingCutoff_compact (n : ℕ) : HasCompactSupport (bindingCutoff n) := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : Configuration n) 2)
  intro x hx
  apply bindingCutoff_eq_zero
  simpa [Metric.mem_closedBall, dist_zero_right] using hx

theorem bindingCutoff_derivative_bounded (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖fderiv ℝ (bindingCutoff n) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := (bindingCutoff_smooth n).continuous_fderiv (by simp)
    |>.bounded_above_of_compact_support ((bindingCutoff_compact n).fderiv ℝ)
  exact ⟨C, (norm_nonneg _).trans (hC 0), hC⟩

theorem bindingScale_pos (k : ℕ) : 0 < bindingScale k :=
  inv_pos.mpr (by positivity)

theorem bindingScale_le_one (k : ℕ) : bindingScale k ≤ 1 := by
  apply inv_le_one_of_one_le₀
  have := Nat.cast_nonneg (α := ℝ) k
  linarith

theorem bindingScale_tendsto : Tendsto bindingScale atTop (𝓝 0) := by
  exact tendsto_inv_atTop_zero.comp
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)

theorem expandingCutoff_smooth (n k : ℕ) : ContDiff ℝ ∞ (expandingCutoff n k) := by
  apply (bindingCutoff_smooth n).comp
  exact (contDiff_const (c := bindingScale k)).smul contDiff_id

theorem expandingCutoff_nonneg (n k : ℕ) (x : Configuration n) :
    0 ≤ expandingCutoff n k x := bindingCutoff_nonneg _ _

theorem expandingCutoff_le_one (n k : ℕ) (x : Configuration n) :
    expandingCutoff n k x ≤ 1 := bindingCutoff_le_one _ _

theorem expandingCutoff_fderiv (n k : ℕ) (x v : Configuration n) :
    fderiv ℝ (expandingCutoff n k) x v =
      bindingScale k * fderiv ℝ (bindingCutoff n) (bindingScale k • x) v := by
  have hf := ((bindingCutoff_smooth n).differentiable (by simp) (bindingScale k • x)).hasFDerivAt
  have hc := (hasFDerivAt_id (𝕜 := ℝ) x).const_smul (bindingScale k)
  have hh := (hf.comp x hc).fderiv
  change fderiv ℝ (bindingCutoff n ∘ fun x => bindingScale k • x) x v = _
  rw [hh]
  simp

theorem expandingCutoff_multiplier (n k : ℕ) : SmoothMultiplier (expandingCutoff n k) := by
  refine ⟨expandingCutoff_smooth n k, ?_, ⟨1, fun x => ?_⟩, ?_⟩
  · intro p x
    exact bindingCutoff_symmetric n p (bindingScale k • x)
  · rw [abs_of_nonneg (expandingCutoff_nonneg _ _ _)]
    exact expandingCutoff_le_one _ _ _
  · intro i a
    obtain ⟨C, hC, hb⟩ := bindingCutoff_derivative_bounded n
    refine ⟨C*‖coordinateDirection i a‖, fun x => ?_⟩
    rw [expandingCutoff_fderiv, abs_mul, abs_of_pos (bindingScale_pos k)]
    calc
      bindingScale k * |fderiv ℝ (bindingCutoff n) (bindingScale k • x)
          (coordinateDirection i a)| ≤
          1*(C*‖coordinateDirection i a‖) := by
        apply mul_le_mul (bindingScale_le_one k) _ (abs_nonneg _) (by norm_num)
        exact ((fderiv ℝ (bindingCutoff n) (bindingScale k • x)).le_opNorm _).trans
          (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
      _ = _ := one_mul _

theorem expandingCutoff_tendsto (n : ℕ) (x : Configuration n) :
    Tendsto (fun k => expandingCutoff n k x) atTop (𝓝 1) := by
  have ht := ((bindingCutoff_smooth n).continuous.tendsto 0).comp
    (by simpa using bindingScale_tendsto.smul_const x)
  simpa [Function.comp_def, expandingCutoff, bindingCutoff_eq_one (by simp : ‖(0 : Configuration n)‖ ≤ 1)] using ht

theorem expandingCutoff_fderiv_tendsto (n : ℕ) (x v : Configuration n) :
    Tendsto (fun k => fderiv ℝ (expandingCutoff n k) x v) atTop (𝓝 0) := by
  simp_rw [expandingCutoff_fderiv]
  have ht := (((bindingCutoff_smooth n).continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := v))).tendsto 0 |>.comp (by simpa using bindingScale_tendsto.smul_const x)
  simpa using bindingScale_tendsto.mul ht

theorem expandingCutoff_eq_zero {n k : ℕ} {x : Configuration n}
    (hx : 2*((k:ℝ)+1) < ‖x‖) : expandingCutoff n k x = 0 := by
  apply bindingCutoff_eq_zero
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (bindingScale_pos k)]
  dsimp [bindingScale]
  rw [← div_eq_inv_mul]
  exact (lt_div_iff₀ (by positivity)).mpr hx

theorem expandingCutoff_derivative_uniform_bound (n : ℕ) (i : Fin n) (a : Fin 3) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k x,
      |fderiv ℝ (expandingCutoff n k) x (coordinateDirection i a)| ≤ C := by
  obtain ⟨C, hC, hb⟩ := bindingCutoff_derivative_bounded n
  refine ⟨C*‖coordinateDirection i a‖, mul_nonneg hC (norm_nonneg _), fun k x => ?_⟩
  rw [expandingCutoff_fderiv, abs_mul, abs_of_pos (bindingScale_pos k)]
  calc
    _ ≤ 1*(C*‖coordinateDirection i a‖) := by
      apply mul_le_mul (bindingScale_le_one k) _ (abs_nonneg _) (by norm_num)
      exact ((fderiv ℝ (bindingCutoff n) (bindingScale k • x)).le_opNorm _).trans
        (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
    _ = _ := one_mul _

theorem integral_expandingCutoff_sq_tendsto {n : ℕ} {f : Configuration n → ℝ}
    (hf : Integrable f) :
    Tendsto (fun k => ∫ x, (expandingCutoff n k x)^2 * f x) atTop (𝓝 (∫ x, f x)) := by
  apply tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
  · intro k
    exact ((expandingCutoff_smooth n k).continuous.aestronglyMeasurable.pow 2).mul
      hf.aestronglyMeasurable
  · exact hf.norm
  · intro k
    exact Eventually.of_forall fun x => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀
        (expandingCutoff_nonneg _ _ _) (expandingCutoff_le_one _ _ _))
  · exact Eventually.of_forall fun x => by
      simpa using ((expandingCutoff_tendsto n x).pow 2).mul_const (f x)

theorem normSquared_cutoff_tendsto {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) :
    Tendsto (fun k => normSquared (multiplyWavefunction (expandingCutoff n k) ψ))
      atTop (𝓝 (normSquared ψ)) := by
  simp only [normSquared, norm_multiplyWavefunction_sq]
  exact tendsto_finsetSum _ fun σ _ =>
    integral_expandingCutoff_sq_tendsto (hd.2.2.1 σ).norm.integrable_sq

theorem kinetic_cutoff_tendsto {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) (σ : Spins n) (i : Fin n) (a : Fin 3) :
    Tendsto (fun k => ∫ x, ‖multiplyGradient (expandingCutoff n k) ψ g σ i a x‖^2)
      atTop (𝓝 (∫ x, ‖g σ i a x‖^2)) := by
  obtain ⟨C, hC, hb⟩ := expandingCutoff_derivative_uniform_bound n i a
  apply tendsto_integral_of_dominated_convergence
    (fun x => 2*C^2*‖ψ σ x‖^2 + 2*‖g σ i a x‖^2)
  · intro k
    exact ((hd.multiply (expandingCutoff_multiplier n k)).2.2.2.1 σ i a).norm.aestronglyMeasurable.pow 2
  · exact ((hd.2.2.1 σ).norm.integrable_sq.const_mul (2*C^2)).add
      ((hd.2.2.2.1 σ i a).norm.integrable_sq.const_mul 2)
  · intro k
    exact Eventually.of_forall fun x => by
      have h1 : ‖multiplyGradient (expandingCutoff n k) ψ g σ i a x‖ ≤
          C*‖ψ σ x‖+‖g σ i a x‖ := by
        unfold multiplyGradient
        apply (norm_add_le _ _).trans
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (expandingCutoff_nonneg _ _ _)]
        exact add_le_add (mul_le_mul_of_nonneg_right (hb k x) (norm_nonneg _))
          (mul_le_of_le_one_left (norm_nonneg _) (expandingCutoff_le_one _ _ _))
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      nlinarith [sq_nonneg (C*‖ψ σ x‖-‖g σ i a x‖)]
  · exact Eventually.of_forall fun x => by
      have h1 := (expandingCutoff_fderiv_tendsto n x (coordinateDirection i a)).smul_const (ψ σ x)
      have h2 := (expandingCutoff_tendsto n x).smul_const (g σ i a x)
      simpa [multiplyGradient] using (h1.add h2).norm.pow 2

theorem energy_cutoff_tendsto {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormDomain ψ g) :
    Tendsto (fun k => energy Z (multiplyWavefunction (expandingCutoff n k) ψ)
      (multiplyGradient (expandingCutoff n k) ψ g)) atTop (𝓝 (energy Z ψ g)) := by
  apply Tendsto.add
  · apply Tendsto.const_mul
    exact tendsto_finsetSum _ fun σ _ => tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun a _ => kinetic_cutoff_tendsto hd σ i a
  · apply tendsto_finsetSum
    intro σ _
    have h := integral_expandingCutoff_sq_tendsto (hd.integrable_potential Z σ)
    convert h using 1
    all_goals try with_reducible_and_instances rfl
    funext k
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [norm_multiplyWavefunction_sq]; ring

theorem expandingCutoff_fderiv_eq_zero {n k : ℕ} {x : Configuration n}
    (hx : 2*((k:ℝ)+1) < ‖x‖) : fderiv ℝ (expandingCutoff n k) x = 0 := by
  have he : expandingCutoff n k =ᶠ[𝓝 x] (fun _ => 0) := by
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hx] with y hy
    exact expandingCutoff_eq_zero hy
  simpa using he.fderiv_eq

theorem FormDomain.exists_compact_approximation {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (χ : Wavefunction n) (h : Gradient n), 0 < R ∧
      FormDomain χ h ∧ normSquared χ = 1 ∧ energy Z χ h < energy Z ψ g + ε ∧
      (∀ σ x, R < ‖x‖ → χ σ x = 0) ∧
      (∀ σ i a x, R < ‖x‖ → h σ i a x = 0) := by
  let χ : ℕ → Wavefunction n := fun k => multiplyWavefunction (expandingCutoff n k) ψ
  let h : ℕ → Gradient n := fun k => multiplyGradient (expandingCutoff n k) ψ g
  let c : ℕ → ℝ := fun k => (Real.sqrt (normSquared (χ k)))⁻¹
  have hnorm : Tendsto (fun k => normSquared (χ k)) atTop (𝓝 1) := by
    simpa [hn] using normSquared_cutoff_tendsto hd
  have hc : Tendsto c atTop (𝓝 1) := by
    have ht := (Real.continuous_sqrt.tendsto 1).comp hnorm
    have hi := ht.inv₀ (by norm_num : Real.sqrt (1 : ℝ) ≠ 0)
    simpa [c] using hi
  have he : Tendsto (fun k => energy Z (scaleWavefunction (c k) (χ k))
      (scaleGradient (c k) (h k))) atTop (𝓝 (energy Z ψ g)) := by
    simp_rw [energy_scale]
    simpa only [one_pow, one_mul] using (hc.pow 2).mul (energy_cutoff_tendsto Z hd)
  have hpos : ∀ᶠ k in atTop, 0 < normSquared (χ k) :=
    hnorm.eventually (Ioi_mem_nhds (by norm_num))
  have hclose : ∀ᶠ k in atTop, energy Z (scaleWavefunction (c k) (χ k))
      (scaleGradient (c k) (h k)) < energy Z ψ g + ε :=
    he.eventually (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  obtain ⟨k, hkpos, hkclose⟩ := (hpos.and hclose).exists
  refine ⟨2*((k:ℝ)+1), scaleWavefunction (c k) (χ k), scaleGradient (c k) (h k),
    by positivity, (hd.multiply (expandingCutoff_multiplier n k)).scale _, ?_, hkclose, ?_, ?_⟩
  · rw [normSquared_scale]
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt hkpos.le, inv_mul_cancel₀ hkpos.ne']
  · intro σ x hx
    simp [scaleWavefunction, χ, multiplyWavefunction, expandingCutoff_eq_zero hx]
  · intro σ i a x hx
    simp [scaleGradient, h, multiplyGradient, expandingCutoff_eq_zero hx,
      expandingCutoff_fderiv_eq_zero hx]

theorem memLp_two_real_tensor {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} [SFinite μ] [SFinite ν]
    {f : A → ℝ} {g : B → ℂ} (hf : MemLp f 2 μ) (hg : MemLp g 2 ν) :
    MemLp (fun z : A×B => f z.1 • g z.2) 2 (μ.prod ν) := by
  apply (memLp_two_iff_integrable_sq_norm
    (hf.aestronglyMeasurable.comp_fst.smul hg.aestronglyMeasurable.comp_snd)).mpr
  change Integrable (fun z : A×B => ‖f z.1 • g z.2‖^2) (μ.prod ν)
  simpa only [norm_smul, mul_pow] using
    hf.norm.integrable_sq.mul_prod hg.norm.integrable_sq

section ProductWeakDerivative
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
theorem compact_support_partial_right {φ : E×F → ℝ}
    (hφ : HasCompactSupport φ) (y : E) : HasCompactSupport (fun x => φ (y,x)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight y, ?_⟩
  have he : Set.range (Prod.mk y : F → E×F) = {y} ×ˢ Set.univ := by
    ext ⟨a,b⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_singleton.prod isClosed_univ

omit [NormedSpace ℝ E] [NormedSpace ℝ F] [MeasureSpace E] [BorelSpace E]
  [Measure.IsAddHaarMeasure (volume : Measure E)] [MeasureSpace F] [BorelSpace F]
  [Measure.IsAddHaarMeasure (volume : Measure F)] [FiniteDimensional ℝ E]
  [FiniteDimensional ℝ F] in
theorem compact_support_partial_left {φ : E×F → ℝ}
    (hφ : HasCompactSupport φ) (x : F) : HasCompactSupport (fun y => φ (y,x)) := by
  apply hφ.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft x, ?_⟩
  have he : Set.range (fun y : E => (y,x)) = Set.univ ×ˢ {x} := by
    ext ⟨a,b⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_univ.prod isClosed_singleton

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_partial_right {φ : E×F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y : E) (x v : F) : fderiv ℝ (fun z => φ (y,z)) x v =
      fderiv ℝ φ (y,x) (0,v) := by
  have hc := (hasFDerivAt_const (𝕜 := ℝ) y x).prodMk (hasFDerivAt_id x)
  exact congrArg (fun A : F →L[ℝ] ℝ => A v)
    (((hφ.differentiable (by simp) (y,x)).hasFDerivAt.comp x hc).fderiv)

omit [MeasureSpace E] [BorelSpace E] [Measure.IsAddHaarMeasure (volume : Measure E)]
  [MeasureSpace F] [BorelSpace F] [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem fderiv_partial_left {φ : E×F → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (y v : E) (x : F) : fderiv ℝ (fun z => φ (z,x)) y v =
      fderiv ℝ φ (y,x) (v,0) := by
  have hc := (hasFDerivAt_id (𝕜 := ℝ) y).prodMk (hasFDerivAt_const x y)
  exact congrArg (fun A : E →L[ℝ] ℝ => A v)
    (((hφ.differentiable (by simp) (y,x)).hasFDerivAt.comp y hc).fderiv)

theorem WeakDirectionalDerivative.tensor_right {ψ g : F → ℂ} {v : F}
    (hd : WeakDirectionalDerivative ψ g v) (hψ : MemLp ψ 2 volume) (hg : MemLp g 2 volume)
    {f : E → ℝ} (hf : MemLp f 2 volume) :
    WeakDirectionalDerivative (fun z : E×F => f z.1 • ψ z.2)
      (fun z : E×F => f z.1 • g z.2) (0,v) := by
  intro φ hφ hφc
  dsimp only
  have hLp := memLp_two_real_tensor hf hψ
  have hgLp := memLp_two_real_tensor hf hg
  have hi₁ : Integrable (fun z : E×F => fderiv ℝ φ z (0,v) • (f z.1 • ψ z.2)) :=
    (hLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hi₂ : Integrable (fun z : E×F => φ z • (f z.1 • g z.2)) :=
    (hgLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφc
  change (∫ z : E×F, fderiv ℝ φ z (0,v) • (f z.1 • ψ z.2) ∂(volume.prod volume)) =
    -(∫ z : E×F, φ z • (f z.1 • g z.2) ∂(volume.prod volume))
  rw [integral_prod _ hi₁, integral_prod _ hi₂, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    have hs := hd (fun x => φ (y,x)) (hφ.comp (contDiff_const.prodMk contDiff_id))
      (compact_support_partial_right hφc y)
    simp_rw [fderiv_partial_right hφ y] at hs
    simp_rw [smul_comm _ (f y), integral_smul]
    simpa only [smul_neg] using congrArg (fun z : ℂ => f y • z) hs

theorem smooth_tensor_weak_left {f : E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfLp : MemLp f 2 volume) (u : E)
    (hdfLp : MemLp (fun y => fderiv ℝ f y u) 2 volume)
    {ψ : F → ℂ} (hψ : MemLp ψ 2 volume) :
    WeakDirectionalDerivative (fun z : E×F => f z.1 • ψ z.2)
      (fun z : E×F => fderiv ℝ f z.1 u • ψ z.2) (u,0) := by
  intro φ hφ hφc
  dsimp only
  have hLp := memLp_two_real_tensor hfLp hψ
  have hgLp := memLp_two_real_tensor hdfLp hψ
  have hi₁ : Integrable (fun z : E×F => fderiv ℝ φ z (u,0) • (f z.1 • ψ z.2)) :=
    (hLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hi₂ : Integrable (fun z : E×F => φ z • (fderiv ℝ f z.1 u • ψ z.2)) :=
    (hgLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
      hφ.continuous hφc
  change (∫ z : E×F, fderiv ℝ φ z (u,0) • (f z.1 • ψ z.2) ∂(volume.prod volume)) =
    -(∫ z : E×F, φ z • (fderiv ℝ f z.1 u • ψ z.2) ∂(volume.prod volume))
  rw [integral_prod_symm _ hi₁, integral_prod_symm _ hi₂, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    let φx : E → ℝ := fun y => φ (y,x)
    have hs : ContDiff ℝ ∞ φx := hφ.comp (contDiff_id.prodMk contDiff_const)
    have hsc : HasCompactSupport φx := compact_support_partial_left hφc x
    have hfd : Continuous (fun y => fderiv ℝ φx y u) :=
      (hs.continuous_fderiv (by simp)).clm_apply continuous_const
    have hid : Integrable (fun y => fderiv ℝ φx y u * f y) :=
      (hfLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
        hfd (hsc.fderiv_apply ℝ _)
    have hid' : Integrable (fun y => fderiv ℝ f y u * φx y) := by
      simpa only [smul_eq_mul, mul_comm] using
        (hdfLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
          hs.continuous hsc
    have hi : Integrable (fun y => f y * φx y) := by
      simpa only [smul_eq_mul, mul_comm] using
        (hfLp.locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
          hs.continuous hsc
    have hh := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := u)
      hid' (by simpa only [mul_comm] using hid) hi
      (fun y _ => hf.differentiable (by simp) y) (fun y _ => hs.differentiable (by simp) y)
    have hh' : (∫ y, fderiv ℝ φ (y,x) (u,0) * f y) =
        -(∫ y, φ (y,x) * fderiv ℝ f y u) := by
      simpa only [φx, fderiv_partial_left hφ, mul_comm] using hh
    simp_rw [smul_smul]
    rw [integral_smul_const, integral_smul_const, hh', neg_smul]

omit [Measure.IsAddHaarMeasure (volume : Measure E)]
  [Measure.IsAddHaarMeasure (volume : Measure F)]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem WeakDirectionalDerivative.comp_equiv {ψ g : F → ℂ} {v : F}
    (hd : WeakDirectionalDerivative ψ g v) (e : E ≃L[ℝ] F)
    (he : MeasurePreserving e) :
    WeakDirectionalDerivative (ψ ∘ e) (g ∘ e) (e.symm v) := by
  intro φ hφ hφc
  have hc := hφ.comp e.symm.contDiff
  have hcc : HasCompactSupport (φ ∘ e.symm) :=
    hφc.comp_homeomorph e.symm.toHomeomorph
  have hdφ : ∀ y, fderiv ℝ (φ ∘ e.symm) y v = fderiv ℝ φ (e.symm y) (e.symm v) := by
    intro y
    rw [((hφ.differentiable (by simp) (e.symm y)).hasFDerivAt.comp y
      e.symm.hasFDerivAt).fderiv]
    rfl
  have hint := hd (φ ∘ e.symm) hc hcc
  simp_rw [hdφ] at hint
  dsimp only [Function.comp_apply] at hint
  rw [← he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun y => fderiv ℝ φ (e.symm y) (e.symm v) • ψ y),
    ← he.integral_comp e.toHomeomorph.measurableEmbedding
      (fun y => φ (e.symm y) • g y)] at hint
  simpa only [ContinuousLinearEquiv.symm_apply_apply, Function.comp_apply] using hint

end ProductWeakDerivative

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_ConfigurationSplit
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 theorem configurationSplit_preserving (n : ℕ) : MeasurePreserving (configurationSplit n) := by
  have h := volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => Position) 0
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  funext x
  change (x 0, fun i => x i.succ) = (x 0, fun i => x (Fin.succAbove 0 i))
  simp only [Fin.succAbove_zero]

 theorem configurationPerm_preserving {n : ℕ} (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (configurationPerm p) :=
  (volume_measurePreserving_piCongrLeft (fun _ : Fin n => Position) p).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n => Position) p)

 theorem configurationPerm_symm_direction {n : ℕ} (p : Equiv.Perm (Fin n))
    (i : Fin n) (a : Fin 3) :
    (configurationPerm p).symm (coordinateDirection (p.symm i) a) = coordinateDirection i a := by
  rw [← configurationPerm_direction, ContinuousLinearEquiv.symm_apply_apply]

 theorem HasWeakGradient.permute {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (p : Equiv.Perm (Fin n)) :
    HasWeakGradient (permuteWavefunction p ψ) (permuteGradient p g) := by
  intro σ i a φ hφ hφc
  have hd : WeakDirectionalDerivative (ψ (σ ∘ p)) (g (σ ∘ p) (p.symm i) a)
      (coordinateDirection (p.symm i) a) := by
    intro η hη hηc
    simpa only [Complex.real_smul, Complex.ofReal_mul] using hg (σ ∘ p) (p.symm i) a η hη hηc
  have ht := hd.comp_equiv (configurationPerm p) (configurationPerm_preserving p)
  rw [configurationPerm_symm_direction] at ht
  simpa only [permuteWavefunction, permuteGradient, Function.comp_apply,
    configurationPerm_apply, Complex.real_smul, Complex.ofReal_mul] using ht φ hφ hφc

 theorem half_ordered_sum {n : ℕ} (F : Fin n → Fin n → ℝ)
    (hF : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), F i j) =
      (1/2:ℝ) * ∑ i : Fin n, ∑ j : Fin n, F i j := by
  classical
  have he : ∀ i j, F i j = (if i < j then F i j else 0) + (if j < i then F j i else 0) := by
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, not_lt.mpr hij.le]
    · simp [hdiag]
    · simp [hji, not_lt.mpr hji.le, hF]
  have hs : (∑ i : Fin n, ∑ j : Fin n, F i j) =
      2 * (∑ i : Fin n, ∑ j : Fin n, if i < j then F i j else 0) := by
    conv_lhs => arg 2; ext i; arg 2; ext j; rw [he i j]
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => if j < i then F j i else 0)]
    ring
  simp only [Finset.sum_filter]
  rw [hs]
  ring

 theorem coulombPotential_permute {n : ℕ} (Z : ℕ) (p : Equiv.Perm (Fin n))
    (x : Configuration n) : coulombPotential Z (x ∘ p) = coulombPotential Z x := by
  have hn : (∑ i : Fin n, ‖x (p i)‖⁻¹) = ∑ i : Fin n, ‖x i‖⁻¹ :=
    Equiv.sum_comp p (fun i => ‖x i‖⁻¹)
  have hs (y : Configuration n) :
      (∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j => i < j), ‖y i-y j‖⁻¹) =
      (1/2:ℝ) * ∑ i : Fin n, ∑ j : Fin n, ‖y i-y j‖⁻¹ :=
    half_ordered_sum _ (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  have hp : (∑ i : Fin n, ∑ j : Fin n, ‖x (p i)-x (p j)‖⁻¹) =
      ∑ i : Fin n, ∑ j : Fin n, ‖x i-x j‖⁻¹ := by
    calc
      _ = ∑ i : Fin n, ∑ j : Fin n, ‖x (p i)-x j‖⁻¹ := by
        apply Finset.sum_congr rfl
        intro i _
        exact Equiv.sum_comp p (fun j => ‖x (p i)-x j‖⁻¹)
      _ = _ := Equiv.sum_comp p (fun i => ∑ j : Fin n, ‖x i-x j‖⁻¹)
  simp only [coulombPotential, hs, Function.comp_apply, hn, hp]

 theorem HasWeakGradient.insert {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hg : HasWeakGradient ψ g) (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    (hgLp : ∀ σ i a, MemLp (g σ i a) 2 volume) {f : Position → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfLp : MemLp f 2 volume)
    (hdfLp : ∀ a : Fin 3, MemLp (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) 2 volume) :
    HasWeakGradient (insertWavefunction f ψ) (insertGradient f ψ g) := by
  intro σ i a φ hφ hφc
  by_cases hσ : σ 0 = 0
  · let τ : Spins n := fun j => σ j.succ
    cases i using Fin.cases with
    | zero =>
      have ht := (smooth_tensor_weak_left hf hfLp (EuclideanSpace.single a 1) (hdfLp a)
        (hψ τ)).comp_equiv (configurationSplit n) (configurationSplit_preserving n)
      have hv : (configurationSplit n).symm (EuclideanSpace.single a 1, 0) =
          coordinateDirection 0 a := by
        apply (configurationSplit n).injective
        rw [ContinuousLinearEquiv.apply_symm_apply, configurationSplit_direction_zero]
      rw [hv] at ht
      simpa only [insertWavefunction, insertGradient, hσ, ↓reduceIte, Fin.cases_zero,
        configurationSplit_apply, Function.comp_apply, Complex.real_smul] using ht φ hφ hφc
    | succ i =>
      have hd : WeakDirectionalDerivative (ψ τ) (g τ i a) (coordinateDirection i a) := by
        intro η hη hηc
        simpa only [Complex.real_smul] using hg τ i a η hη hηc
      have ht := (hd.tensor_right (hψ τ) (hgLp τ i a) hfLp).comp_equiv
        (configurationSplit n) (configurationSplit_preserving n)
      have hv : (configurationSplit n).symm (0, coordinateDirection i a) =
          coordinateDirection i.succ a := by
        apply (configurationSplit n).injective
        rw [ContinuousLinearEquiv.apply_symm_apply, configurationSplit_direction_succ]
      rw [hv] at ht
      simpa only [insertWavefunction, insertGradient, hσ, ↓reduceIte, Fin.cases_succ,
        configurationSplit_apply, Function.comp_apply, Complex.real_smul] using ht φ hφ hφc
  · simp [insertWavefunction, insertGradient, hσ]

 theorem insertWavefunction_memLp {n : ℕ} {ψ : Wavefunction n} (hψ : ∀ σ, MemLp (ψ σ) 2 volume)
    {f : Position → ℝ} (hf : MemLp f 2 volume) (σ : Spins (n+1)) :
    MemLp (insertWavefunction f ψ σ) 2 volume := by
  by_cases hσ : σ 0 = 0
  · have he : insertWavefunction f ψ σ =
        (fun z : Position×Configuration n => f z.1 • ψ (fun i => σ i.succ) z.2) ∘
          configurationSplit n := by
      funext x
      simp [insertWavefunction, hσ]
    rw [he]
    exact (memLp_two_real_tensor hf (hψ (fun i => σ i.succ))).comp_measurePreserving
      (configurationSplit_preserving n)
  · have he : insertWavefunction f ψ σ = fun _ => 0 := by
      funext x
      simp [insertWavefunction, hσ]
    rw [he]
    exact MemLp.zero'

 theorem insertGradient_memLp {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hψ : ∀ σ, MemLp (ψ σ) 2 volume) (hg : ∀ σ i a, MemLp (g σ i a) 2 volume)
    {f : Position → ℝ} (hf : MemLp f 2 volume)
    (hdf : ∀ a : Fin 3, MemLp (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) 2 volume)
    (σ : Spins (n+1)) (i : Fin (n+1)) (a : Fin 3) :
    MemLp (insertGradient f ψ g σ i a) 2 volume := by
  by_cases hσ : σ 0 = 0
  · cases i using Fin.cases with
    | zero =>
      have he : insertGradient f ψ g σ 0 a =
          (fun z : Position×Configuration n => fderiv ℝ f z.1 (EuclideanSpace.single a 1) •
            ψ (fun j => σ j.succ) z.2) ∘ configurationSplit n := by
        funext x
        simp [insertGradient, hσ]
      rw [he]
      exact (memLp_two_real_tensor (hdf a) (hψ (fun j => σ j.succ))).comp_measurePreserving
        (configurationSplit_preserving n)
    | succ i =>
      have he : insertGradient f ψ g σ i.succ a =
          (fun z : Position×Configuration n => f z.1 •
            g (fun j => σ j.succ) i a z.2) ∘ configurationSplit n := by
        funext x
        simp [insertGradient, hσ]
      rw [he]
      exact (memLp_two_real_tensor hf (hg (fun j => σ j.succ) i a)).comp_measurePreserving
        (configurationSplit_preserving n)
  · have he : insertGradient f ψ g σ i a = fun _ => 0 := by
      funext x
      simp [insertGradient, hσ]
    rw [he]
    exact MemLp.zero'

 theorem integral_tensor_norm {n : ℕ} (f : Position → ℝ) (ψ : Configuration n → ℂ) :
    (∫ x : Configuration (n+1), ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
      (∫ y : Position, (f y)^2) * ∫ x : Configuration n, ‖ψ x‖^2 := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z : Position × Configuration n => ‖f z.1 • ψ z.2‖^2)
  change (∫ x : Configuration (n+1), ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
    ∫ z : Position × Configuration n, ‖f z.1 • ψ z.2‖^2 at he
  rw [he]
  simp_rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  exact integral_prod_mul (μ := volume) (ν := volume)
    (fun y : Position => (f y)^2) (fun x : Configuration n => ‖ψ x‖^2)

 theorem normSquared_insert {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n) :
    normSquared (insertWavefunction f ψ) = (∫ y : Position, (f y)^2) * normSquared ψ := by
  classical
  unfold normSquared
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, insertWavefunction, Fin.cons_zero,
    Fin.cons_succ, h10, ↓reduceIte]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), integral_zero,
    Finset.sum_const_zero, add_zero, integral_tensor_norm, Finset.mul_sum]

 theorem FormRegular.pair {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) (σ : Spins n) (i j : Fin n) :
    Integrable (fun x : Configuration n => ‖x i-x j‖⁻¹ * ‖ψ σ x‖^2) := by
  rcases lt_trichotomy i j with hij | rfl | hji
  · exact h.2.2.2.2 σ i j hij
  · simp
  · simpa only [norm_sub_rev] using h.2.2.2.2 σ j i hji

 theorem FormRegular.permute {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) (p : Equiv.Perm (Fin n)) :
    FormRegular (permuteWavefunction p ψ) (permuteGradient p g) := by
  refine ⟨h.1.permute p, ?_, ?_, ?_, ?_⟩
  · intro σ
    exact (h.2.1 (σ ∘ p)).comp_measurePreserving (configurationPerm_preserving p)
  · intro σ i a
    exact (h.2.2.1 (σ ∘ p) (p.symm i) a).comp_measurePreserving (configurationPerm_preserving p)
  · intro σ i
    have ht := (configurationPerm_preserving p).integrable_comp_of_integrable
      (h.2.2.2.1 (σ ∘ p) (p.symm i))
    simpa only [Function.comp_def, configurationPerm_apply, Equiv.apply_symm_apply,
      permuteWavefunction] using ht
  · intro σ i j _
    have ht := (configurationPerm_preserving p).integrable_comp_of_integrable
      (h.pair (σ ∘ p) (p.symm i) (p.symm j))
    simpa only [Function.comp_def, configurationPerm_apply, Equiv.apply_symm_apply,
      permuteWavefunction] using ht

 theorem WeakDirectionalDerivative.finite_sum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)] [FiniteDimensional ℝ E]
    {ι : Type*} [Fintype ι] (c : ι → ℝ) {ψ g : ι → E → ℂ} {v : E}
    (hd : ∀ i, WeakDirectionalDerivative (ψ i) (g i) v)
    (hψ : ∀ i, MemLp (ψ i) 2 volume) (hg : ∀ i, MemLp (g i) 2 volume) :
    WeakDirectionalDerivative (fun x => ∑ i, c i • ψ i x) (fun x => ∑ i, c i • g i x) v := by
  intro φ hφ hφc
  have hi (i : ι) : Integrable (fun x => fderiv ℝ φ x v • (c i • ψ i x)) :=
    ((hψ i).const_smul (c i)).locallyIntegrable (by norm_num)
      |>.integrable_smul_left_of_hasCompactSupport
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const) (hφc.fderiv_apply ℝ _)
  have hi' (i : ι) : Integrable (fun x => φ x • (c i • g i x)) :=
    ((hg i).const_smul (c i)).locallyIntegrable (by norm_num)
      |>.integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  dsimp only
  simp_rw [Finset.smul_sum]
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hi' i),
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp_rw [smul_comm _ (c i), integral_smul]
  simpa only [smul_neg] using congrArg (fun z : ℂ => c i • z) (hd i φ hφ hφc)

 theorem integrable_weighted_norm_sum {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {ι : Type*} [Fintype ι] {W : A → ℝ} (hW : Measurable W) (hW0 : ∀ x, 0 ≤ W x)
    (c : ι → ℝ) {f : ι → A → ℂ} (hf : ∀ i, AEStronglyMeasurable (f i) μ)
    (hi : ∀ i, Integrable (fun x => W x * ‖f i x‖^2) μ) :
    Integrable (fun x => W x * ‖∑ i, c i • f i x‖^2) μ := by
  have hroot : Measurable (fun x => Real.sqrt (W x)) := Real.continuous_sqrt.measurable.comp hW
  have he : ∀ i, MemLp (fun x => Real.sqrt (W x) • f i x) 2 μ := by
    intro i
    apply (memLp_two_iff_integrable_sq_norm (hroot.aestronglyMeasurable.smul (hf i))).mpr
    change Integrable (fun x => ‖Real.sqrt (W x) • f i x‖^2) μ
    simpa only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hW0 _)] using hi i
  have hs := memLp_finsetSum Finset.univ (fun i _ => (he i).const_smul (c i))
  have hint := hs.norm.integrable_sq
  have hx : (fun x => ‖∑ i, c i • (Real.sqrt (W x) • f i x)‖^2) =
      (fun x => W x * ‖∑ i, c i • f i x‖^2) := by
    funext x
    simp_rw [smul_comm (c _) (Real.sqrt (W x)), ← Finset.smul_sum]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hW0 x)]
  exact hx ▸ hint

 theorem FormRegular.finite_sum {n : ℕ} {ι : Type*} [Fintype ι] (c : ι → ℝ)
    {ψ : ι → Wavefunction n} {g : ι → Gradient n} (h : ∀ j, FormRegular (ψ j) (g j)) :
    FormRegular (sumWavefunction c ψ) (sumGradient c g) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro σ i a φ hφ hφc
    have hd (j : ι) : WeakDirectionalDerivative (ψ j σ) (g j σ i a) (coordinateDirection i a) := by
      intro η hη hηc
      simpa only [Complex.real_smul] using (h j).1 σ i a η hη hηc
    simpa only [sumWavefunction, sumGradient, Complex.real_smul] using
      (WeakDirectionalDerivative.finite_sum c hd (fun j => (h j).2.1 σ)
        (fun j => (h j).2.2.1 σ i a)) φ hφ hφc
  · intro σ
    exact memLp_finsetSum Finset.univ (fun j _ => ((h j).2.1 σ).const_smul (c j))
  · intro σ i a
    exact memLp_finsetSum Finset.univ (fun j _ => ((h j).2.2.1 σ i a).const_smul (c j))
  · intro σ i
    exact integrable_weighted_norm_sum (by fun_prop) (fun x => inv_nonneg.mpr (norm_nonneg _)) c
      (fun j => ((h j).2.1 σ).aestronglyMeasurable) (fun j => (h j).2.2.2.1 σ i)
  · intro σ i k hik
    exact integrable_weighted_norm_sum (by fun_prop) (fun x => inv_nonneg.mpr (norm_nonneg _)) c
      (fun j => ((h j).2.1 σ).aestronglyMeasurable) (fun j => (h j).2.2.2.2 σ i k hik)

 theorem antisymmetrize_antisymmetric {n : ℕ} (ψ : Wavefunction n) :
    IsAntisymmetric (antisymmetrize ψ) := by
  intro q σ
  apply Eventually.of_forall
  intro x
  have he (p : Equiv.Perm (Fin n)) :
      permutationSign p = permutationSign q * permutationSign (q*p) := by
    rw [permutationSign_mul, ← mul_assoc, permutationSign_sq, one_mul]
  change (∑ p : Equiv.Perm (Fin n), permutationSign p • ψ ((σ ∘ q) ∘ p) ((x ∘ q) ∘ p)) =
    ((Equiv.Perm.sign q : ℤ) : ℂ) * ∑ p : Equiv.Perm (Fin n),
      permutationSign p • ψ (σ ∘ p) (x ∘ p)
  calc
    _ = ∑ p : Equiv.Perm (Fin n), permutationSign q •
        (permutationSign (q*p) • ψ (σ ∘ (q*p : Equiv.Perm (Fin n))) (x ∘ (q*p : Equiv.Perm (Fin n)))) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [smul_smul, ← he p]
      rfl
    _ = permutationSign q • ∑ p : Equiv.Perm (Fin n),
        permutationSign (q*p) • ψ (σ ∘ (q*p : Equiv.Perm (Fin n))) (x ∘ (q*p : Equiv.Perm (Fin n))) := by rw [Finset.smul_sum]
    _ = permutationSign q • ∑ p : Equiv.Perm (Fin n),
        permutationSign p • ψ (σ ∘ p) (x ∘ p) := by
      exact congrArg (fun z : ℂ => permutationSign q • z)
        (Equiv.sum_comp (Equiv.mulLeft q)
          (fun p : Equiv.Perm (Fin n) => permutationSign p • ψ (σ ∘ p) (x ∘ p)))
    _ = _ := by simp only [permutationSign, Complex.real_smul, Complex.ofReal_intCast]

 theorem configurationTail_quasiPreserving (n : ℕ) :
    Measure.QuasiMeasurePreserving (fun x : Configuration (n+1) => fun i : Fin n => x i.succ)
      volume volume :=
  Measure.quasiMeasurePreserving_snd.comp (configurationSplit_preserving n).quasiMeasurePreserving

 theorem permutationSign_decompose {n : ℕ} (i : Fin (n+1)) (p : Equiv.Perm (Fin n)) :
    permutationSign (Equiv.Perm.decomposeFin.symm (i,p)) =
      permutationSign (Equiv.swap 0 i) * permutationSign p := by
  have he := Equiv.Perm.decomposeFin_symm_of_one i
  rw [← he]
  by_cases hi : i = 0
  · simp [permutationSign, Equiv.Perm.decomposeFin.symm_sign, hi]
  · simp [permutationSign, Equiv.Perm.decomposeFin.symm_sign, hi, Ne.symm hi]

 theorem insert_permute_decompose {n : ℕ} {ψ : Wavefunction n} (hψ : IsAntisymmetric ψ)
    (f : Position → ℝ) (i : Fin (n+1)) (p : Equiv.Perm (Fin n)) (σ : Spins (n+1)) :
    permuteWavefunction (Equiv.Perm.decomposeFin.symm (i,p)) (insertWavefunction f ψ) σ =ᵐ[volume]
      (fun x => permutationSign p • permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ x) := by
  let τ : Spins n := fun j => σ (Equiv.swap 0 i j.succ)
  have hp := (hψ p τ).comp_tendsto
    ((configurationTail_quasiPreserving n).comp
      (configurationPerm_preserving (Equiv.swap 0 i)).quasiMeasurePreserving).tendsto_ae
  filter_upwards [hp] with x hx
  change ψ (τ ∘ p) ((fun j => x (Equiv.swap 0 i j.succ)) ∘ p) =
    ((Equiv.Perm.sign p : ℤ) : ℂ) * ψ τ (fun j => x (Equiv.swap 0 i j.succ)) at hx
  simp only [permuteWavefunction, insertWavefunction, Function.comp_apply,
    Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.decomposeFin_symm_apply_succ,
    Equiv.swap_apply_left]
  by_cases hσ : σ i = 0
  · simp only [hσ, ↓reduceIte]
    change f (x i) • ψ (τ ∘ p) ((fun j => x (Equiv.swap 0 i j.succ)) ∘ p) = _
    rw [hx]
    simp only [permutationSign, Complex.real_smul, Complex.ofReal_intCast]
    ring
  · simp [hσ]

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Variational_WedgeInsert
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 theorem antisymmetrize_insert_eq {n : ℕ} {ψ : Wavefunction n} (hψ : IsAntisymmetric ψ)
    (f : Position → ℝ) (σ : Spins (n+1)) :
    antisymmetrize (insertWavefunction f ψ) σ =ᵐ[volume]
      (fun x => (n.factorial : ℝ) • wedgeInsert f ψ σ x) := by
  classical
  have hi : ∀ᵐ x : Configuration (n+1) ∂volume, ∀ i : Fin (n+1), ∀ p : Equiv.Perm (Fin n),
      permutationSign (Equiv.Perm.decomposeFin.symm (i,p)) •
        permuteWavefunction (Equiv.Perm.decomposeFin.symm (i,p)) (insertWavefunction f ψ) σ x =
      permutationSign (Equiv.swap 0 i) • permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ x := by
    apply (ae_all_iff).mpr
    intro i
    apply (ae_all_iff).mpr
    intro p
    filter_upwards [insert_permute_decompose hψ f i p σ] with x hx
    rw [hx, permutationSign_decompose, smul_smul]
    simp only [mul_assoc, permutationSign_sq, mul_one]
  filter_upwards [hi] with x hx
  unfold antisymmetrize sumWavefunction wedgeInsert
  rw [← Equiv.sum_comp Equiv.Perm.decomposeFin.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [hx]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    sumWavefunction, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Complex.real_smul, nsmul_eq_mul, Complex.ofReal_natCast]

 theorem insertionSupport_tensor {n : ℕ} {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} (hf : ∀ y, ‖y‖ ≤ R → f y = 0)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0) :
    InsertionSupport R (insertWavefunction f ψ) := by
  intro σ x hx
  have hi : σ 0 = 0 := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hh])
  have hf0 : f (x 0) ≠ 0 := by
    intro hh
    exact hx (by simp [insertWavefunction, hh])
  have hψ0 : ψ (fun i => σ i.succ) (fun i => x i.succ) ≠ 0 := by
    intro hh
    exact hx (by simp [insertWavefunction, hh])
  have htail : ‖fun i : Fin n => x i.succ‖ ≤ R := by
    by_contra hh
    exact hψ0 (hψ _ _ (lt_of_not_ge hh))
  exact ⟨lt_of_not_ge (fun hh => hf0 (hf _ hh)), fun i => (norm_le_pi_norm _ i).trans htail⟩

 theorem InsertionSupport.swap {n : ℕ} {R : ℝ} {F : Wavefunction (n+1)}
    (hF : InsertionSupport R F) {σ : Spins (n+1)} {x : Configuration (n+1)}
    {i : Fin (n+1)} (hi : permuteWavefunction (Equiv.swap 0 i) F σ x ≠ 0) :
    R < ‖x i‖ ∧ ∀ j, j ≠ i → ‖x j‖ ≤ R := by
  have h := hF (σ ∘ Equiv.swap 0 i) (x ∘ Equiv.swap 0 i) hi
  refine ⟨by simpa only [Function.comp_apply, Equiv.swap_apply_left] using h.1, ?_⟩
  intro j hji
  have hne : Equiv.swap 0 i j ≠ 0 := by
    intro hh
    have he := congrArg (Equiv.swap 0 i) hh
    exact hji (by simpa only [Equiv.swap_apply_self, Equiv.swap_apply_left] using he)
  have hg : ∀ k : Fin (n+1), k ≠ 0 → ‖x (Equiv.swap 0 i k)‖ ≤ R := by
    intro k hk
    cases k using Fin.cases with
    | zero => exact (hk rfl).elim
    | succ k => exact h.2 k
  simpa only [Equiv.swap_apply_self] using hg _ hne

 theorem InsertionSupport.placements_disjoint {n : ℕ} {R : ℝ} {F G : Wavefunction (n+1)}
    (hF : InsertionSupport R F) (hG : InsertionSupport R G) (σ : Spins (n+1))
    (x : Configuration (n+1)) {i j : Fin (n+1)} (hij : i ≠ j) :
    permuteWavefunction (Equiv.swap 0 i) F σ x = 0 ∨
      permuteWavefunction (Equiv.swap 0 j) G σ x = 0 := by
  by_contra hh
  have hi := hF.swap (not_or.mp hh).1
  have hj := hG.swap (not_or.mp hh).2
  exact (not_lt_of_ge (hj.2 i hij)) hi.1

 theorem norm_sq_sum_of_disjoint {ι : Type*} [Fintype ι] (v : ι → ℂ)
    (hv : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i, v i‖^2 = ∑ i, ‖v i‖^2 := by
  classical
  by_cases he : ∃ i, v i ≠ 0
  · obtain ⟨i,hi⟩ := he
    have hz : ∀ j, j ≠ i → v j = 0 := fun j hji => (hv j i hji).resolve_right hi
    rw [Finset.sum_eq_single i, Finset.sum_eq_single i]
    · intro j _ hji
      simp [hz j hji]
    · simp
    · intro j _ hji
      exact hz j hji
    · simp
  · have hz : ∀ i, v i = 0 := by simpa using he
    simp [hz]

 theorem normSquared_permute {n : ℕ} (p : Equiv.Perm (Fin n)) (ψ : Wavefunction n) :
    normSquared (permuteWavefunction p ψ) = normSquared ψ := by
  unfold normSquared permuteWavefunction
  have hi (σ : Spins n) := (configurationPerm_preserving p).integral_comp
    (configurationPerm p).toHomeomorph.measurableEmbedding (fun x => ‖ψ (σ ∘ p) x‖^2)
  simp only [configurationPerm_apply] at hi
  simp_rw [hi]
  exact Equiv.sum_comp (spinsPerm p) (fun σ => ∫ x, ‖ψ σ x‖^2)

 theorem energy_permute {n : ℕ} (Z : ℕ) (p : Equiv.Perm (Fin n))
    (ψ : Wavefunction n) (g : Gradient n) :
    energy Z (permuteWavefunction p ψ) (permuteGradient p g) = energy Z ψ g := by
  have hi (σ : Spins n) (i : Fin n) (a : Fin 3) :=
    (configurationPerm_preserving p).integral_comp
      (configurationPerm p).toHomeomorph.measurableEmbedding (fun x => ‖g (σ ∘ p) (p.symm i) a x‖^2)
  simp only [configurationPerm_apply] at hi
  have hv (σ : Spins n) := (configurationPerm_preserving p).integral_comp
    (configurationPerm p).toHomeomorph.measurableEmbedding
    (fun x => coulombPotential Z x * ‖ψ (σ ∘ p) x‖^2)
  simp only [configurationPerm_apply, coulombPotential_permute] at hv
  unfold energy permuteWavefunction permuteGradient
  simp_rw [hi, hv]
  congr 1
  · congr 1
    have hs (σ : Spins n) : (∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ (p.symm i) a x‖^2) =
        ∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2 :=
      Equiv.sum_comp p.symm (fun i => ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2)
    simp_rw [hs]
    exact Equiv.sum_comp (spinsPerm p) (fun σ => ∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2)
  · exact Equiv.sum_comp (spinsPerm p) (fun σ => ∫ x, coulombPotential Z x * ‖ψ σ x‖^2)

 theorem norm_sq_sum_real_smul_of_disjoint {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (v : ι → ℂ) (hv : ∀ i j, i ≠ j → v i = 0 ∨ v j = 0) :
    ‖∑ i, c i • v i‖^2 = ∑ i, (c i)^2 * ‖v i‖^2 := by
  rw [norm_sq_sum_of_disjoint (fun i => c i • v i)]
  · simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  · intro i j hij
    rcases hv i j hij with hi | hj
    · exact Or.inl (by rw [hi, smul_zero])
    · exact Or.inr (by rw [hj, smul_zero])

 theorem FormRegular.integrable_potential {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hd : FormRegular ψ g) (Z : ℕ) (σ : Spins n) :
    Integrable (fun x : Configuration n => coulombPotential Z x*‖ψ σ x‖^2) := by
  have hn := integrable_finsetSum Finset.univ (fun i _ => hd.2.2.2.1 σ i)
  have hp := integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum (Finset.univ.filter (fun j => i < j))
      (fun j hj => hd.2.2.2.2 σ i j (Finset.mem_filter.mp hj).2))
  apply ((hn.const_mul (-(Z:ℝ))).add hp).congr
  exact Eventually.of_forall fun x => by
    simp only [Pi.add_apply, coulombPotential, add_mul, Finset.sum_mul, mul_assoc]

 theorem normSquared_disjoint_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) {ψ : ι → Wavefunction n} (hψ : ∀ i σ, MemLp (ψ i σ) 2 volume)
    (hd : ∀ σ x i j, i ≠ j → ψ i σ x = 0 ∨ ψ j σ x = 0) :
    normSquared (sumWavefunction c ψ) = ∑ i, (c i)^2 * normSquared (ψ i) := by
  unfold normSquared sumWavefunction
  simp_rw [norm_sq_sum_real_smul_of_disjoint c _ (hd _ _)]
  simp_rw [integral_finsetSum _ (fun i _ => ((hψ i _).norm.integrable_sq).const_mul ((c i)^2)),
    integral_const_mul]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]

 theorem energy_disjoint_sum {n : ℕ} {ι : Type*} [Fintype ι]
    (Z : ℕ) (c : ι → ℝ) {ψ : ι → Wavefunction n} {g : ι → Gradient n}
    (h : ∀ i, FormRegular (ψ i) (g i))
    (hd : ∀ σ x i j, i ≠ j → ψ i σ x = 0 ∨ ψ j σ x = 0)
    (hdg : ∀ σ k a x i j, i ≠ j → g i σ k a x = 0 ∨ g j σ k a x = 0) :
    energy Z (sumWavefunction c ψ) (sumGradient c g) = ∑ i, (c i)^2 * energy Z (ψ i) (g i) := by
  have hk (σ : Spins n) (k : Fin n) (a : Fin 3) :
      (∫ x, ‖sumGradient c g σ k a x‖^2) =
        ∑ i, (c i)^2 * ∫ x, ‖g i σ k a x‖^2 := by
    simp only [sumGradient]
    simp_rw [norm_sq_sum_real_smul_of_disjoint c _ (hdg _ _ _ _)]
    rw [integral_finsetSum _ (fun i _ => ((h i).2.2.1 σ k a).norm.integrable_sq.const_mul ((c i)^2))]
    simp only [integral_const_mul]
  have hv (σ : Spins n) :
      (∫ x, coulombPotential Z x * ‖sumWavefunction c ψ σ x‖^2) =
        ∑ i, (c i)^2 * ∫ x, coulombPotential Z x * ‖ψ i σ x‖^2 := by
    simp only [sumWavefunction]
    simp_rw [norm_sq_sum_real_smul_of_disjoint c _ (hd _ _), Finset.mul_sum]
    simp_rw [← mul_assoc, mul_comm (coulombPotential Z _) ((c _)^2), mul_assoc]
    rw [integral_finsetSum _ (fun i _ => ((h i).integrable_potential Z σ).const_mul ((c i)^2))]
    simp only [integral_const_mul]
  unfold energy
  simp_rw [hk, hv]
  have hs : (∑ σ : Spins n, ∑ k : Fin n, ∑ a : Fin 3, ∑ i, (c i)^2 * ∫ x, ‖g i σ k a x‖^2) =
      ∑ i, (c i)^2 * ∑ σ : Spins n, ∑ k : Fin n, ∑ a : Fin 3, ∫ x, ‖g i σ k a x‖^2 := by
    simp_rw [Finset.sum_comm (f := fun a i => (c i)^2 * ∫ x, ‖g i _ _ a x‖^2)]
    simp_rw [Finset.sum_comm (f := fun k i => ∑ a : Fin 3, (c i)^2 * ∫ x, ‖g i _ k a x‖^2)]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [hs, Finset.sum_comm (f := fun σ i => (c i)^2 * ∫ x, coulombPotential Z x * ‖ψ i σ x‖^2)]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.mul_sum]
  ring

 theorem insertionSupport_gradient {n : ℕ} {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} {g : Gradient n} (hf : ∀ y, ‖y‖ ≤ R → f y = 0)
    (hdf : ∀ a y, ‖y‖ ≤ R → fderiv ℝ f y (EuclideanSpace.single a 1) = 0)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    (hg : ∀ σ i a x, R < ‖x‖ → g σ i a x = 0) (i : Fin (n+1)) (a : Fin 3) :
    InsertionSupport R (fun σ x => insertGradient f ψ g σ i a x) := by
  cases i using Fin.cases with
  | zero => exact insertionSupport_tensor (hdf a) hψ
  | succ i => exact insertionSupport_tensor hf (fun σ x hx => hg σ i a x hx)

 theorem wedgeInsert_antisymmetric {n : ℕ} {ψ : Wavefunction n} (hψ : IsAntisymmetric ψ)
    (f : Position → ℝ) : IsAntisymmetric (wedgeInsert f ψ) := by
  intro p σ
  have hl := (antisymmetrize_insert_eq hψ f (σ ∘ p)).comp_tendsto
    (configurationPerm_preserving p).quasiMeasurePreserving.tendsto_ae
  filter_upwards [hl, antisymmetrize_insert_eq hψ f σ,
    antisymmetrize_antisymmetric (insertWavefunction f ψ) p σ] with x hx hy hz
  change antisymmetrize (insertWavefunction f ψ) (σ ∘ p) (x ∘ p) = _ at hx
  rw [hx, hy] at hz
  simp only [Complex.real_smul, Complex.ofReal_natCast] at hz
  have hc : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  apply mul_left_cancel₀ hc
  simpa only [Function.comp_apply, configurationPerm_apply,
    mul_left_comm ((Equiv.Perm.sign p : ℤ) : ℂ)] using hz

 theorem FormRegular.wedgeInsert {n : ℕ} {f : Position → ℝ} {ψ : Wavefunction n} {g : Gradient n}
    (hψ : IsAntisymmetric ψ) (h : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    FormDomain (wedgeInsert f ψ) (wedgeInsertGradient f ψ g) :=
  ⟨wedgeInsert_antisymmetric hψ f,
    FormRegular.finite_sum (fun i => permutationSign (Equiv.swap 0 i))
      (fun i => h.permute (Equiv.swap 0 i))⟩

 theorem normSquared_wedgeInsert {n : ℕ} {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} (hψLp : ∀ σ, MemLp (ψ σ) 2 volume) (hfLp : MemLp f 2 volume)
    (hs : InsertionSupport R (insertWavefunction f ψ)) :
    normSquared (wedgeInsert f ψ) = (n+1 : ℝ) * normSquared (insertWavefunction f ψ) := by
  have hLp (i : Fin (n+1)) (σ : Spins (n+1)) :
      MemLp (permuteWavefunction (Equiv.swap 0 i) (insertWavefunction f ψ) σ) 2 volume :=
    (insertWavefunction_memLp hψLp hfLp _).comp_measurePreserving
      (configurationPerm_preserving (Equiv.swap 0 i))
  unfold wedgeInsert
  rw [normSquared_disjoint_sum _ hLp (fun σ x i j hij => hs.placements_disjoint hs σ x hij)]
  simp only [pow_two, permutationSign_sq, one_mul, normSquared_permute, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

 theorem energy_wedgeInsert {n : ℕ} (Z : ℕ) {R : ℝ} {f : Position → ℝ}
    {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g))
    (hs : InsertionSupport R (insertWavefunction f ψ))
    (hsg : ∀ i a, InsertionSupport R (fun σ x => insertGradient f ψ g σ i a x)) :
    energy Z (wedgeInsert f ψ) (wedgeInsertGradient f ψ g) =
      (n+1 : ℝ) * energy Z (insertWavefunction f ψ) (insertGradient f ψ g) := by
  unfold wedgeInsert wedgeInsertGradient
  rw [energy_disjoint_sum Z _ (fun i => h.permute (Equiv.swap 0 i))
    (fun σ x i j hij => hs.placements_disjoint hs σ x hij)
    (fun σ k a x i j hij => (hsg ((Equiv.swap 0 i).symm k) a).placements_disjoint
      (hsg ((Equiv.swap 0 j).symm k) a) σ x hij)]
  simp only [pow_two, permutationSign_sq, one_mul, energy_permute, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]

 theorem integrable_supported_weight {A : Type*} [MeasurableSpace A] {μ : Measure A}
    {ψ : A → ℂ} (hψ : MemLp ψ 2 μ) {W : A → ℝ} (hW : Measurable W)
    {C : ℝ} (hb : ∀ x, ψ x ≠ 0 → |W x| ≤ C) :
    Integrable (fun x => W x * ‖ψ x‖^2) μ := by
  apply (hψ.norm.integrable_sq.const_mul C).mono'
    (hW.aestronglyMeasurable.mul (hψ.aestronglyMeasurable.norm.pow 2))
  apply Eventually.of_forall
  intro x
  by_cases hx : ψ x = 0
  · simp [hx]
  · change ‖W x * ‖ψ x‖^2‖ ≤ C * ‖ψ x‖^2
    simpa only [Real.norm_eq_abs, abs_mul, abs_pow, abs_norm] using
      mul_le_mul_of_nonneg_right (hb x hx) (sq_nonneg ‖ψ x‖)

 theorem integrable_weighted_tensor {n : ℕ} {f : Position → ℝ} (hf : MemLp f 2 volume)
    {ψ : Configuration n → ℂ} {W : Configuration n → ℝ}
    (hW : Integrable (fun x => W x * ‖ψ x‖^2)) :
    Integrable (fun x : Configuration (n+1) => W (fun i => x i.succ) *
      ‖f (x 0) • ψ (fun i => x i.succ)‖^2) := by
  have hi : Integrable (fun z : Position × Configuration n => (f z.1)^2 * (W z.2 * ‖ψ z.2‖^2)) :=
    hf.integrable_sq.mul_prod hW
  have hp := (configurationSplit_preserving n).integrable_comp_of_integrable hi
  apply hp.congr
  exact Eventually.of_forall fun x => by
    simp only [Function.comp_apply, configurationSplit_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring

 theorem integral_weighted_tensor {n : ℕ} (f : Position → ℝ)
    (ψ : Configuration n → ℂ) (W : Configuration n → ℝ) :
    (∫ x : Configuration (n+1), W (fun i => x i.succ) * ‖f (x 0) • ψ (fun i => x i.succ)‖^2) =
      (∫ y : Position, (f y)^2) * ∫ x : Configuration n, W x * ‖ψ x‖^2 := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z : Position × Configuration n => (f z.1)^2 * (W z.2 * ‖ψ z.2‖^2))
  have hi := integral_prod_mul (μ := (volume : Measure Position)) (ν := (volume : Measure (Configuration n)))
    (fun y => (f y)^2) (fun x => W x * ‖ψ x‖^2)
  rw [← hi]
  change _ = ∫ z : Position × Configuration n, (f z.1)^2 * (W z.2 * ‖ψ z.2‖^2)
  rw [← he]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [configurationSplit_apply, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring

 theorem inserted_nuclear_bound {n : ℕ} {d : ℝ} (hd : 0 < d)
    {f : Position → ℝ} {ψ : Wavefunction n} (hf : ∀ y, ‖y‖ ≤ d → f y = 0)
    (σ : Spins (n+1)) (x : Configuration (n+1)) (hx : insertWavefunction f ψ σ x ≠ 0) :
    |‖x 0‖⁻¹| ≤ d⁻¹ := by
  have hdf : d < ‖x 0‖ := by
    by_contra hh
    have hhf := hf (x 0) (le_of_not_gt hh)
    exact hx (by simp [insertWavefunction, hhf])
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
    one_div_le_one_div_of_le hd hdf.le

 theorem inserted_pair_bound {n : ℕ} {R d : ℝ} (hRd : R < d)
    {f : Position → ℝ} {ψ : Wavefunction n} (hf : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    (σ : Spins (n+1)) (x : Configuration (n+1)) (i : Fin n)
    (hx : insertWavefunction f ψ σ x ≠ 0) : |‖x 0-x i.succ‖⁻¹| ≤ (d-R)⁻¹ := by
  have hdf : d < ‖x 0‖ := by
    by_contra hh
    exact hx (by simp [insertWavefunction, hf (x 0) (le_of_not_gt hh)])
  have htail := (insertionSupport_tensor (fun y hy => hf y (hy.trans hRd.le)) hψ σ x hx).2 i
  have hb := norm_sub_norm_le (x 0) (x i.succ)
  have hdist : d-R ≤ ‖x 0-x i.succ‖ := by linarith
  simpa only [one_div, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))] using
    one_div_le_one_div_of_le (sub_pos.mpr hRd) hdist

 theorem FormRegular.insert_separated {n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) {R d : ℝ} (hd : 0 < d) (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hf : ContDiff ℝ ∞ f) (hfLp : MemLp f 2 volume)
    (hdfLp : ∀ a, MemLp (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) 2 volume)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0) :
    FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) := by
  refine ⟨HasWeakGradient.insert h.1 h.2.1 h.2.2.1 hf hfLp hdfLp,
    insertWavefunction_memLp h.2.1 hfLp, insertGradient_memLp h.2.1 h.2.2.1 hfLp hdfLp, ?_, ?_⟩
  · intro σ i
    cases i using Fin.cases with
    | zero =>
      exact integrable_supported_weight (insertWavefunction_memLp h.2.1 hfLp σ)
        (by fun_prop) (inserted_nuclear_bound hd hfout σ)
    | succ i =>
      by_cases hσ : σ 0 = 0
      · simpa only [insertWavefunction, hσ, ↓reduceIte] using
          integrable_weighted_tensor hfLp (h.2.2.2.1 (fun i => σ i.succ) i)
      · simp [insertWavefunction, hσ]
  · intro σ i j hij
    cases i using Fin.cases with
    | zero =>
      cases j using Fin.cases with
      | zero => exact (lt_irrefl _ hij).elim
      | succ j =>
        exact integrable_supported_weight (insertWavefunction_memLp h.2.1 hfLp σ)
          (by fun_prop) (inserted_pair_bound hRd hfout hψ σ · j)
    | succ i =>
      cases j using Fin.cases with
      | zero => exact (not_lt_of_ge (Fin.zero_le _) hij).elim
      | succ j =>
        by_cases hσ : σ 0 = 0
        · simpa only [insertWavefunction, hσ, ↓reduceIte] using
            integrable_weighted_tensor hfLp (h.pair (fun i => σ i.succ) i j)
        · simp [insertWavefunction, hσ]

 theorem coulombPotential_cons {n : ℕ} (Z : ℕ) (y : Position) (x : Configuration n) :
    coulombPotential Z (Fin.cons y x) = coulombPotential Z x - (Z : ℝ)*‖y‖⁻¹ +
      ∑ i : Fin n, ‖y-x i‖⁻¹ := by
  have hs {k : ℕ} (z : Configuration k) :
      (∑ i : Fin k, ∑ j ∈ Finset.univ.filter (fun j => i < j), ‖z i-z j‖⁻¹) =
      (1/2:ℝ) * ∑ i : Fin k, ∑ j : Fin k, ‖z i-z j‖⁻¹ :=
    half_ordered_sum _ (fun i j => by rw [norm_sub_rev]) (fun i => by simp)
  simp only [coulombPotential, hs, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    sub_self, norm_zero, inv_zero, zero_add, Finset.sum_add_distrib]
  simp_rw [norm_sub_rev _ y]
  ring

 theorem gradientNormSquared_eq {n : ℕ} (g : Gradient n) :
    gradientNormSquared g = ∑ σ : Spins n, ∑ i : Fin n, ∑ a : Fin 3, ∫ x, ‖g σ i a x‖^2 := by
  unfold gradientNormSquared normSquared
  simp_rw [Finset.sum_comm (f := fun a σ => ∫ x, ‖g σ _ a x‖^2)]
  rw [Finset.sum_comm]

 theorem energy_decompose {n : ℕ} (Z : ℕ) (ψ : Wavefunction n) (g : Gradient n) :
    energy Z ψ g = (1/2 : ℝ)*gradientNormSquared g + potentialForm Z ψ := by
  rw [gradientNormSquared_eq]
  rfl

end NeutralAtom
end
end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FormDomain_ParticleGradientNorm
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology ContDiff
namespace NeutralAtom

 theorem gradientNormSquared_insert {n : ℕ} (f : Position → ℝ)
    (ψ : Wavefunction n) (g : Gradient n) :
    gradientNormSquared (insertGradient f ψ g) =
      (∫ y : Position, (f y)^2) * gradientNormSquared g + oneParticleGradientNorm f * normSquared ψ := by
  unfold gradientNormSquared
  rw [Fin.sum_univ_succ]
  change (∑ a : Fin 3, normSquared (insertWavefunction (fun y => fderiv ℝ f y (EuclideanSpace.single a 1)) ψ)) +
      (∑ i : Fin n, ∑ a : Fin 3, normSquared (insertWavefunction f (fun σ x => g σ i a x))) = _
  simp only [normSquared_insert, oneParticleGradientNorm, Finset.sum_mul, Finset.mul_sum]
  ring

 theorem weighted_normSquared_insert {n : ℕ} (f : Position → ℝ) (ψ : Wavefunction n)
    (W : Configuration n → ℝ) :
    (∑ σ : Spins (n+1), ∫ x : Configuration (n+1),
      W (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2) =
      (∫ y : Position, (f y)^2) * ∑ σ : Spins n, ∫ x : Configuration n, W x*‖ψ σ x‖^2 := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, insertWavefunction, Fin.cons_zero,
    Fin.cons_succ, h10, ↓reduceIte]
  simp only [norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero, integral_zero,
    Finset.sum_const_zero, add_zero, integral_weighted_tensor, Finset.mul_sum]

 theorem potentialForm_insert_le {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) {R d : ℝ} (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hfLp : MemLp f 2 volume)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    potentialForm Z (insertWavefunction f ψ) ≤
      (∫ y : Position, (f y)^2) * potentialForm Z ψ +
        ((n : ℝ)*(d-R)⁻¹)*normSquared (insertWavefunction f ψ) := by
  let C : ℝ := (n : ℝ)*(d-R)⁻¹
  have hold (σ : Spins (n+1)) : Integrable (fun x : Configuration (n+1) =>
      coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2) := by
    by_cases hσ : σ 0 = 0
    · simpa only [insertWavefunction, hσ, ↓reduceIte] using
        integrable_weighted_tensor hfLp (h.integrable_potential Z (fun i => σ i.succ))
    · simp [insertWavefunction, hσ]
  have hnew (σ : Spins (n+1)) := ((hi.2.1 σ).norm.integrable_sq).const_mul C
  have hb (σ : Spins (n+1)) (x : Configuration (n+1)) :
      coulombPotential Z x*‖insertWavefunction f ψ σ x‖^2 ≤
        coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2 +
          C*‖insertWavefunction f ψ σ x‖^2 := by
    by_cases hx : insertWavefunction f ψ σ x = 0
    · simp [hx]
    · have he : x = Fin.cons (x 0) (fun i => x i.succ) := by ext i; cases i using Fin.cases <;> rfl
      have hsum : (∑ i : Fin n, ‖x 0-x i.succ‖⁻¹) ≤ C := by
        calc
          _ ≤ ∑ _i : Fin n, (d-R)⁻¹ := Finset.sum_le_sum fun i _ =>
            (le_abs_self _).trans (inserted_pair_bound hRd hfout hψ σ x i hx)
          _ = C := by simp [C]
      have hpot : coulombPotential Z x ≤ coulombPotential Z (fun i => x i.succ) + C := by
        conv_lhs => rw [he, coulombPotential_cons]
        have hn : 0 ≤ (Z : ℝ)*‖x 0‖⁻¹ := by positivity
        linarith
      simpa only [add_mul] using mul_le_mul_of_nonneg_right hpot (sq_nonneg ‖insertWavefunction f ψ σ x‖)
  have hiσ (σ : Spins (n+1)) :
      (∫ x, coulombPotential Z x*‖insertWavefunction f ψ σ x‖^2) ≤
        (∫ x, coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2) +
          C*(∫ x, ‖insertWavefunction f ψ σ x‖^2) := by
    have hm := integral_mono (hi.integrable_potential Z σ) ((hold σ).add (hnew σ)) (hb σ)
    change _ ≤ ∫ x, coulombPotential Z (fun i => x i.succ)*‖insertWavefunction f ψ σ x‖^2 +
      C*‖insertWavefunction f ψ σ x‖^2 at hm
    rw [integral_add (hold σ) (hnew σ), integral_const_mul] at hm
    exact hm
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun σ _ => hiσ σ)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [weighted_normSquared_insert] at hsum
  exact hsum

 theorem energy_insert_le {n : ℕ} (Z : ℕ) {ψ : Wavefunction n} {g : Gradient n}
    (h : FormRegular ψ g) (hn : normSquared ψ = 1) {R d : ℝ} (hRd : R < d)
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    {f : Position → ℝ} (hfLp : MemLp f 2 volume) (hfn : (∫ y : Position, (f y)^2) = 1)
    (hfout : ∀ y, ‖y‖ ≤ d → f y = 0)
    (hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g)) :
    energy Z (insertWavefunction f ψ) (insertGradient f ψ g) ≤ energy Z ψ g +
      (1/2 : ℝ)*oneParticleGradientNorm f + (n : ℝ)*(d-R)⁻¹ := by
  have hp := potentialForm_insert_le Z h hRd hψ hfLp hfout hi
  simp only [hfn, normSquared_insert, hn, one_mul, mul_one] at hp
  rw [energy_decompose, energy_decompose, gradientNormSquared_insert, hfn, hn, one_mul, mul_one]
  linarith

theorem distantCenter_norm : ‖distantCenter‖ = 4 := by
  simp [distantCenter, norm_smul, EuclideanSpace.single, PiLp.norm_single]

theorem bindingBump_smooth : ContDiff ℝ ∞ (fun y : Position => bindingBump y) := bindingBump.contDiff

theorem distantMass_pos : 0 < distantMass := by
  have hc : Continuous (fun y : Position => (bindingBump y)^2) :=
    bindingBump_smooth.continuous.pow 2
  have hs : HasCompactSupport (fun y : Position => (bindingBump y)^2) := by
    apply HasCompactSupport.intro (isCompact_closedBall (0 : Position) 2)
    intro y hy
    have hh : 2 ≤ ‖y‖ := (lt_of_not_ge (by simpa [Metric.mem_closedBall, dist_zero_right] using hy)).le
    rw [bindingBump.zero_of_le_dist (by simpa [bindingBump] using hh)]
    norm_num
  apply integral_pos_of_integrable_nonneg_nonzero hc (hc.integrable_of_hasCompactSupport hs)
    (fun y => sq_nonneg _) (x := 0)
  rw [bindingBump.one_of_mem_closedBall (by simp [bindingBump])]
  norm_num

theorem distantPacket_smooth (t : ℝ) : ContDiff ℝ ∞ (distantPacket t) :=
  contDiff_const.mul (bindingBump.contDiff.comp
    (((contDiff_const (c := t⁻¹)).smul (contDiff_id (E := Position))).sub contDiff_const))

theorem distantPacket_compact {t : ℝ} (ht : 0 < t) : HasCompactSupport (distantPacket t) := by
  let u : ℝˣ := Units.mk0 t⁻¹ (inv_ne_zero ht.ne')
  have hc : HasCompactSupport (fun y : Position => bindingBump (t⁻¹ • y - distantCenter)) :=
    (bindingBump.hasCompactSupport.comp_homeomorph (Homeomorph.subRight distantCenter)).comp_homeomorph
      (Homeomorph.smul u)
  exact hc.mul_left

theorem distantPacket_memLp {t : ℝ} (ht : 0 < t) : MemLp (distantPacket t) 2 volume :=
  (distantPacket_smooth t).continuous.memLp_of_hasCompactSupport (distantPacket_compact ht)

theorem distantPacket_derivative_memLp {t : ℝ} (ht : 0 < t) (v : Position) :
    MemLp (fun y => fderiv ℝ (distantPacket t) y v) 2 volume :=
  (((distantPacket_smooth t).continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
    ((distantPacket_compact ht).fderiv_apply ℝ v)

theorem integral_distant_comp {t : ℝ} (ht : 0 < t) (F : Position → ℝ) :
    (∫ y : Position, F (t⁻¹ • y - distantCenter)) = t^3 * ∫ y : Position, F y := by
  rw [show (fun y : Position => F (t⁻¹ • y-distantCenter)) =
      (fun y : Position => (fun z : Position => F (z-distantCenter)) (t⁻¹ • y)) from rfl]
  rw [Measure.integral_comp_smul_of_nonneg volume (fun z : Position => F (z-distantCenter)) t⁻¹ (hR := by positivity)]
  simp [integral_sub_right_eq_self, Position, inv_pow]

theorem distantPacket_normalized {t : ℝ} (ht : 0 < t) :
    (∫ y : Position, (distantPacket t y)^2) = 1 := by
  simp only [distantPacket, mul_pow, integral_const_mul]
  rw [integral_distant_comp ht (fun y => (bindingBump y)^2)]
  rw [inv_pow, Real.sq_sqrt (mul_nonneg (pow_nonneg ht.le 3) distantMass_pos.le)]
  change (t^3*distantMass)⁻¹*(t^3*distantMass) = 1
  exact inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero _ ht.ne') distantMass_pos.ne')

theorem distantPacket_zero {t : ℝ} (ht : 0 < t) {y : Position} (hy : ‖y‖ ≤ 2*t) :
    distantPacket t y = 0 := by
  have hnorm : ‖t⁻¹ • y‖ ≤ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
    exact (inv_mul_le_iff₀ ht).mpr (by nlinarith)
  have hdist : 2 ≤ ‖t⁻¹ • y - distantCenter‖ := by
    have h := norm_sub_norm_le distantCenter (t⁻¹ • y)
    rw [distantCenter_norm, norm_sub_rev] at h
    linarith
  have := bindingBump.zero_of_le_dist (by simpa [bindingBump] using hdist)
  simp [distantPacket, this]

theorem distantPacket_derivative_zero {t : ℝ} (ht : 0 < t) {y : Position}
    (hy : ‖y‖ ≤ t) (v : Position) : fderiv ℝ (distantPacket t) y v = 0 := by
  have he : distantPacket t =ᶠ[𝓝 y] (fun _ => 0) := by
    have hn : ‖y‖ < 2*t := by linarith
    filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hn] with z hz
    exact distantPacket_zero ht hz.le
  rw [he.fderiv_eq]
  simp

theorem distantPacket_fderiv {t : ℝ} (y v : Position) :
    fderiv ℝ (distantPacket t) y v =
      (Real.sqrt (t^3*distantMass))⁻¹ * t⁻¹ *
        fderiv ℝ (fun z : Position => bindingBump z) (t⁻¹ • y-distantCenter) v := by
  have hb := (bindingBump_smooth.differentiable (by simp) (t⁻¹ • y-distantCenter)).hasFDerivAt
  have hc := ((hasFDerivAt_id (𝕜 := ℝ) y).const_smul t⁻¹).sub_const distantCenter
  have hh := ((hb.comp y hc).const_mul (Real.sqrt (t^3*distantMass))⁻¹).fderiv
  change fderiv ℝ (fun y : Position => (Real.sqrt (t^3*distantMass))⁻¹ *
    bindingBump (t⁻¹ • y-distantCenter)) y v = _
  change fderiv ℝ (fun y : Position => (Real.sqrt (t^3*distantMass))⁻¹ *
    (bindingBump ∘ fun x : Position => (t⁻¹ • id) x - distantCenter) y) y v = _
  rw [hh]
  simp [mul_assoc]

theorem distantPacket_gradientNorm {t : ℝ} (ht : 0 < t) :
    oneParticleGradientNorm (distantPacket t) =
      t⁻¹^2 * (distantMass⁻¹ * oneParticleGradientNorm bindingBump) := by
  unfold oneParticleGradientNorm
  simp_rw [distantPacket_fderiv, mul_pow, integral_const_mul]
  have hi (a : Fin 3) := integral_distant_comp ht
    (fun y => (fderiv ℝ (fun z : Position => bindingBump z) y (EuclideanSpace.single a 1))^2)
  simp_rw [hi]
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [inv_pow, Real.sq_sqrt (mul_nonneg (pow_nonneg ht.le 3) distantMass_pos.le)]
  field_simp

theorem distantInsertion_error_tendsto (n : ℕ) (R : ℝ) :
    Tendsto (fun t : ℝ => (1/2 : ℝ) * (t⁻¹^2 *
      (distantMass⁻¹ * oneParticleGradientNorm bindingBump)) + (n : ℝ)*(t-R)⁻¹)
      atTop (𝓝 0) := by
  have hi : Tendsto (fun t : ℝ => (t-R)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp
      (by simpa only [sub_eq_add_neg, id_eq] using tendsto_atTop_add_const_right atTop (-R) tendsto_id)
  have hh := ((tendsto_inv_atTop_zero.pow 2).mul_const
    (distantMass⁻¹ * oneParticleGradientNorm bindingBump)).const_mul (1/2 : ℝ)
  simpa using hh.add (hi.const_mul (n : ℝ))

theorem FormDomain.exists_inserted_trial {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {R : ℝ}
    (hψ : ∀ σ x, R < ‖x‖ → ψ σ x = 0)
    (hg : ∀ σ i a x, R < ‖x‖ → g σ i a x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (χ : Wavefunction (n+1)) (h : Gradient (n+1)),
      FormDomain χ h ∧ normSquared χ = 1 ∧ energy Z χ h < energy Z ψ g + ε := by
  have he : ∀ᶠ t : ℝ in atTop, (1/2 : ℝ) *
      (t⁻¹^2 * (distantMass⁻¹ * oneParticleGradientNorm bindingBump)) + (n : ℝ)*(t-R)⁻¹ < ε :=
    (distantInsertion_error_tendsto n R).eventually (Iio_mem_nhds hε)
  obtain ⟨t, ht, htR, hterr⟩ := ((eventually_gt_atTop (0 : ℝ)).and
    ((eventually_gt_atTop R).and he)).exists
  let f := distantPacket t
  have hfLp : MemLp f 2 volume := distantPacket_memLp ht
  have hfn : (∫ y : Position, (f y)^2) = 1 := distantPacket_normalized ht
  have hfout : ∀ y, ‖y‖ ≤ t → f y = 0 :=
    fun y hy => distantPacket_zero ht (by linarith)
  have hi : FormRegular (insertWavefunction f ψ) (insertGradient f ψ g) :=
    FormRegular.insert_separated hd.2 ht htR hψ (distantPacket_smooth t) hfLp
      (fun a => distantPacket_derivative_memLp ht _) hfout
  have hfs : ∀ y, ‖y‖ ≤ R → f y = 0 := fun y hy => hfout y (hy.trans htR.le)
  have hs := insertionSupport_tensor hfs hψ
  have hgs : ∀ i a, InsertionSupport R (fun σ x => insertGradient f ψ g σ i a x) :=
    insertionSupport_gradient hfs
      (fun a y hy => distantPacket_derivative_zero ht (hy.trans htR.le) _) hψ hg
  let c : ℝ := (Real.sqrt (n+1 : ℝ))⁻¹
  have hc : c^2 * (n+1 : ℝ) = 1 := by
    dsimp [c]
    rw [inv_pow, Real.sq_sqrt (by positivity), inv_mul_cancel₀ (by positivity)]
  refine ⟨scaleWavefunction c (wedgeInsert f ψ), scaleGradient c (wedgeInsertGradient f ψ g),
    (hi.wedgeInsert hd.1).scale c, ?_, ?_⟩
  · rw [normSquared_scale, normSquared_wedgeInsert hd.2.2.1 hfLp hs,
      normSquared_insert, hfn, hn]
    simpa only [one_mul, mul_one] using hc
  · rw [energy_scale, energy_wedgeInsert Z hi hs hgs, ← mul_assoc, hc, one_mul]
    have hh := energy_insert_le Z hd.2 hn htR hψ hfLp hfn hfout hi
    rw [distantPacket_gradientNorm ht] at hh
    linarith

theorem FormDomain.exists_successor_trial {n : ℕ} (Z : ℕ)
    {ψ : Wavefunction n} {g : Gradient n} (hd : FormDomain ψ g)
    (hn : normSquared ψ = 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (χ : Wavefunction (n+1)) (h : Gradient (n+1)),
      FormDomain χ h ∧ normSquared χ = 1 ∧ energy Z χ h < energy Z ψ g + ε := by
  obtain ⟨R, χ, h, _, hχ, hχn, hχe, hχs, hhs⟩ := hd.exists_compact_approximation Z hn
    (half_pos hε)
  obtain ⟨χ', h', hχ', hχ'n, hχ'e⟩ := hχ.exists_inserted_trial Z hχn hχs hhs (half_pos hε)
  exact ⟨χ', h', hχ', hχ'n, by linarith⟩

theorem sectorEnergy_le_trial {Z n : ℕ} {ψ : Wavefunction n} {g : Gradient n}
    (hψ : FormDomain ψ g) (hn : normSquared ψ = 1) :
    sectorEnergy Z n ≤ (energy Z ψ g : EReal) := sInf_le ⟨ψ, g, hψ, hn, rfl⟩

theorem sectorEnergy_succ_le (Z n : ℕ) : sectorEnergy Z (n+1) ≤ sectorEnergy Z n := by
  apply le_sInf
  rintro e ⟨ψ, g, hd, hn, rfl⟩
  by_contra hh
  obtain ⟨r, hEr, hrE⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_of_not_ge hh)
  have hε : 0 < r-energy Z ψ g := sub_pos.mpr (EReal.coe_lt_coe_iff.mp hEr)
  obtain ⟨χ, h, hχ, hχn, hχe⟩ := hd.exists_successor_trial Z hn hε
  have hlt : energy Z χ h < r := by linarith
  have hle := sectorEnergy_le_trial (Z := Z) hχ hχn
  exact (not_lt_of_ge hle) ((EReal.coe_lt_coe_iff.mpr hlt).trans hrE)

theorem sectorEnergy_antitone (Z : ℕ) : Antitone (sectorEnergy Z) :=
  antitone_nat_of_succ_le (sectorEnergy_succ_le Z)

theorem vacuum_volume_univ : (volume : Measure (Configuration 0)) Set.univ = 1 := by
  rw [volume_pi, Measure.pi_univ]
  simp

theorem vacuum_formDomain : FormDomain vacuumWavefunction vacuumGradient := by
  let : IsProbabilityMeasure (volume : Measure (Configuration 0)) := ⟨vacuum_volume_univ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro p σ
    have hp : p = 1 := Subsingleton.elim _ _
    simp [vacuumWavefunction, hp]
  · intro σ i
    exact Fin.elim0 i
  · intro σ
    exact memLp_const _
  · intro σ i
    exact Fin.elim0 i
  · intro σ i
    exact Fin.elim0 i
  · intro σ i
    exact Fin.elim0 i

theorem vacuum_normalized : normSquared vacuumWavefunction = 1 := by
  let : IsProbabilityMeasure (volume : Measure (Configuration 0)) := ⟨vacuum_volume_univ⟩
  simp [normSquared, vacuumWavefunction, Spins]

theorem energy_vacuum_sector (Z : ℕ) (ψ : Wavefunction 0) (g : Gradient 0) : energy Z ψ g = 0 := by
  simp [energy, coulombPotential]

theorem sectorEnergy_vacuum (Z : ℕ) : sectorEnergy Z 0 = 0 := by
  apply le_antisymm
  · simpa [energy_vacuum_sector] using
      sectorEnergy_le_trial (Z := Z) vacuum_formDomain vacuum_normalized
  · apply le_sInf
    rintro e ⟨ψ, g, _, _, rfl⟩
    simp [energy_vacuum_sector]

end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_SectorBottomBridge
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section
open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Classical
namespace NeutralAtom

theorem sectorEnergy_eq_formBottom (Z : ℕ) (hZ : 1≤Z) (n : ℕ) :
    sectorEnergy Z n=Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n := by
  apply le_antisymm
  · apply le_sInf
    rintro e ⟨u,ha,hm,rfl⟩
    have H := sectorEnergy_le_trial (Z:=Z) (fromH1_domain u ha) ((fromH1_mass u).trans hm)
    rwa [fromH1_energy Z hZ] at H
  · apply le_sInf
    rintro e ⟨ψ,g,hd,hn,rfl⟩
    let u := asH1 ψ g hd.2.1 hd.2.2.1 hd.2.2.2.1
    have H : Coulomb.sectorFormBottom (Coulomb.atom Z hZ) n≤
        (Coulomb.form (Coulomb.atom Z hZ) u:EReal) :=
      sInf_le ⟨u,asH1_antisymmetric hd,(asH1_mass ..).trans hn,rfl⟩
    rwa [asH1_energy Z hZ] at H

end NeutralAtom
namespace Coulomb
lemma atom_sectorFormBottom_antitone (Z : ℕ) (hZ : 1≤Z) :
    Antitone (sectorFormBottom (atom Z hZ)) := by
  intro a b hab
  rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,←NeutralAtom.sectorEnergy_eq_formBottom Z hZ]
  exact NeutralAtom.sectorEnergy_antitone Z hab

lemma slice_core_form_ge_sector {J m k : ℕ} (S : Nuclei J) (u : H1Vector (m+k))
    (ha : ∀ s, ∀ᵐ x, Antisymmetric (u.coreSlice s x))
    {P : ℝ} (hP : (P:EReal)≤ sectorFormBottom S k) :
    P*mass u≤ sliceExpectation u (fun s x => form S (u.coreSlice s x).normalized) := by
  rw [←sliceExpectation_number u P]
  apply Finset.sum_le_sum
  intro s _
  apply integral_mono_ae
    (by simpa only [mul_comm (mass _) P] using (mass_coreSlice_integrable u s).const_mul P)
    (normalized_coreForm_weight_integrable S u s)
  filter_upwards [ha s] with x hx
  by_cases hz : mass (u.coreSlice s x)=0
  · simp [hz]
  · have hp := lt_of_le_of_ne (mass_nonneg (u.coreSlice s x)) (Ne.symm hz)
    apply mul_le_mul_of_nonneg_left _ hp.le
    exact EReal.coe_le_coe_iff.mp (hP.trans (sInf_le
      ⟨(u.coreSlice s x).normalized,hx.normalized,mass_normalized _ hp,rfl⟩))

end Coulomb

end
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_AmbientEigen
attribute [-instance] _root_.OAI.Coulomb.finite_volume_ball
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma massPair_congr {n:ℕ} (u v u' v':H1Vector n)
    (hu:∀ s,u.value s=ᵐ[volume]u'.value s) (hv:∀ s,v.value s=ᵐ[volume]v'.value s) :
    massPair u v=massPair u' v' := by
  unfold massPair
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [hu s,hv s] with x hx hy
  rw [hx,hy]
lemma formPair_congr {M n:ℕ} (S:Nuclei M) (u v u' v':H1Vector n)
    (hu:∀ s,u.value s=ᵐ[volume]u'.value s) (hv:∀ s,v.value s=ᵐ[volume]v'.value s) :
    formPair S u v=formPair S u' v' := by
  have he:∀ s,(u.add v).value s=ᵐ[volume](u'.add v').value s:=fun s => (hu s).add (hv s)
  have hh:=form_congr_ae S (u.add v) (u'.add v') he
  linarith [formPair_polarization S u v,formPair_polarization S u' v',form_congr_ae S u u' hu,form_congr_ae S v v' hv]
lemma massPair_symm {n:ℕ} (u v:H1Vector n) : massPair u v=massPair v u := by
  simp only [massPair,real_inner_comm]
lemma formPair_symm {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) : formPair S u v=formPair S v u := by
  simp only [formPair,kineticPair,nuclearPair,repulsionPair,real_inner_comm]
lemma massPair_rsmul_right {n:ℕ} (u v:H1Vector n) (t:ℝ) : massPair u (v.rsmul t)=t*massPair u v := by
  simp only [massPair,H1Vector.rsmul,←Complex.real_smul,real_inner_smul_right,integral_const_mul,Finset.mul_sum]
lemma formPair_rsmul_right {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (t:ℝ) :
    formPair S u (v.rsmul t)=t*formPair S u v := by
  unfold formPair kineticPair nuclearPair repulsionPair
  simp only [H1Vector.rsmul,←Complex.real_smul,real_inner_smul_right]
  simp_rw [mul_left_comm _ t,integral_const_mul,←Finset.mul_sum]
  ring
lemma massPair_rsmul_left {n:ℕ} (u v:H1Vector n) (t:ℝ) : massPair (u.rsmul t) v=t*massPair u v := by
  rw [massPair_symm,massPair_rsmul_right,massPair_symm v u]
lemma formPair_rsmul_left {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (t:ℝ) :
    formPair S (u.rsmul t) v=t*formPair S u v := by
  rw [formPair_symm,formPair_rsmul_right,formPair_symm S v u]
lemma massPair_permutation {n:ℕ} (u v:H1Vector n) (p:Equiv.Perm (Fin n)) :
    massPair (u.permutation p) (v.permutation p)=massPair u v := by
  have he:∀ s,((u.add v).permutation p).value s=ᵐ[volume]((u.permutation p).add (v.permutation p)).value s :=
    fun s => Eventually.of_forall fun x => by simp only [permutation_value,H1Vector.add]
  have hh:=mass_congr_ae _ _ he
  rw [mass_permutation] at hh
  have h:=massPair_polarization (u.permutation p) (v.permutation p)
  rw [mass_permutation,mass_permutation,←hh] at h
  linarith [massPair_polarization u v]
lemma formPair_permutation {M n:ℕ} (S:Nuclei M) (u v:H1Vector n) (p:Equiv.Perm (Fin n)) :
    formPair S (u.permutation p) (v.permutation p)=formPair S u v := by
  have he:∀ s,((u.add v).permutation p).value s=ᵐ[volume]((u.permutation p).add (v.permutation p)).value s :=
    fun s => Eventually.of_forall fun x => by simp only [permutation_value,H1Vector.add]
  have hh:=form_congr_ae S _ _ he
  rw [form_permutation] at hh
  have h:=formPair_polarization S (u.permutation p) (v.permutation p)
  rw [form_permutation,form_permutation,←hh] at h
  linarith [formPair_polarization S u v]
lemma massPair_finiteSum {n:ℕ} {ι:Type*} [Fintype ι] (u:H1Vector n) (v:ι → H1Vector n) :
    massPair u (H1Vector.finiteSum v)=∑ i,massPair u (v i) := by
  unfold massPair
  simp only [H1Vector.finiteSum,inner_sum]
  simp_rw [integral_finsetSum _ (fun i _ => memlp_real_inner_integrable (u.value_L2 _) ((v i).value_L2 _))]
  exact Finset.sum_comm
lemma formPair_finiteSum {M n:ℕ} {ι:Type*} [Fintype ι] (S:Nuclei M) (u:H1Vector n) (v:ι → H1Vector n) :
    formPair S u (H1Vector.finiteSum v)=∑ i,formPair S u (v i) := by
  have hT:kineticPair u (H1Vector.finiteSum v)=∑ i,kineticPair u (v i) := by
    unfold kineticPair
    simp only [H1Vector.finiteSum,inner_sum]
    simp_rw [integral_finsetSum _ (fun i _ => formPair_kinetic_integrable u (v i) _ _)]
    rw [←Finset.mul_sum]
    congr 1
    calc
      _ = ∑ s,∑ i,∑ a,∫ x,inner ℝ (u.gradient s a x) ((v i).gradient s a x) :=
        Finset.sum_congr rfl (fun s _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  have hN:nuclearPair S u (H1Vector.finiteSum v)=∑ i,nuclearPair S u (v i) := by
    unfold nuclearPair
    simp only [H1Vector.finiteSum,inner_sum,Finset.mul_sum]
    simp_rw [integral_finsetSum _ (fun i _ => formPair_nuclear_integrable S u (v i) _)]
    exact Finset.sum_comm
  have hP:repulsionPair u (H1Vector.finiteSum v)=∑ i,repulsionPair u (v i) := by
    unfold repulsionPair
    simp only [H1Vector.finiteSum,inner_sum,Finset.mul_sum]
    simp_rw [integral_finsetSum _ (fun i _ => formPair_repulsion_integrable u (v i) _)]
    exact Finset.sum_comm
  simp only [formPair,hT,hN,hP,Finset.sum_add_distrib,Finset.sum_sub_distrib]

lemma sector_minimizer_ambient_eigen (Z:ℕ) (hZ:1 ≤ Z) {n:ℕ}
    (u:H1Vector n) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) n)
    (v:H1Vector n) :
    formPair (atom Z hZ) u v=form (atom Z hZ) u*massPair u v := by
  let sign:=fun p:Equiv.Perm (Fin n) => ((p.sign:ℤ):ℝ)
  let av:=H1Vector.finiteSum (fun p:Equiv.Perm (Fin n) => (v.permutation p).rsmul (sign p))
  have he:∀ s,av.value s=ᵐ[volume]v.fullAntisymmetrize.value s:= by
    intro s
    exact Eventually.of_forall fun x => by simp [av,fullAntisymmetrize_value,H1Vector.finiteSum,H1Vector.rsmul,sign,permutation_value]
  have hav:Antisymmetric av := by
    intro p s
    filter_upwards [he (s ∘ p) |>.comp_tendsto (permute_measurePreserving p).quasiMeasurePreserving.tendsto_ae,
      he s,fullAntisymmetrize_antisymmetric v p s] with x hx hy hz
    dsimp only [Function.comp_apply] at hx
    rw [hx,hz,←hy]
  have hp(p:Equiv.Perm (Fin n)):∀ s,(u.permutation p).value s=ᵐ[volume](u.rsmul (sign p)).value s := by
    intro s
    filter_upwards [ha p s] with x hx
    simpa only [permutation_value,H1Vector.rsmul,sign,Complex.ofReal_intCast] using hx
  have hform:formPair (atom Z hZ) u av=(Fintype.card (Equiv.Perm (Fin n)):ℝ)*formPair (atom Z hZ) u v := by
    rw [formPair_finiteSum]
    calc
      _ = ∑ _p:Equiv.Perm (Fin n),formPair (atom Z hZ) u v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [formPair_rsmul_right,←formPair_rsmul_left]
        rw [←formPair_congr (atom Z hZ) (u.permutation p) (v.permutation p) _ _ (hp p) (fun _ => EventuallyEq.rfl)]
        exact formPair_permutation _ _ _ _
      _ = _ := by simp
  have hmass:massPair u av=(Fintype.card (Equiv.Perm (Fin n)):ℝ)*massPair u v := by
    rw [massPair_finiteSum]
    calc
      _ = ∑ _p:Equiv.Perm (Fin n),massPair u v := by
        apply Finset.sum_congr rfl
        intro p _
        rw [massPair_rsmul_right,←massPair_rsmul_left]
        rw [←massPair_congr (u.permutation p) (v.permutation p) _ _ (hp p) (fun _ => EventuallyEq.rfl)]
        exact massPair_permutation _ _ _
      _ = _ := by simp
  have H:=sector_minimizer_weak_eigen Z hZ u ha hm hmin av hav
  rw [hform,hmass] at H
  have hc:0<(Fintype.card (Equiv.Perm (Fin n)):ℝ):=by exact_mod_cast Fintype.card_pos
  nlinarith
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma inner_double_real (a:ℂ) (f:ℝ) :
    inner ℝ a ((f:ℂ)*((f:ℂ)*a))=‖(f:ℂ)*a‖^2 := by
  simp only [←Complex.real_smul,real_inner_smul_right,real_inner_self_eq_norm_sq,
    norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
lemma weighted_core_inequality (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    (f:Configuration (1+k) → ℝ) (hf:ContDiff ℝ ∞ f)
    (B D:ℝ) (hB:∀ x,|f x|≤B)
    (hD:∀ a x,|fderiv ℝ f x (EuclideanSpace.single a 1)|≤D)
    (hcore:∀ (a:Fin k × Fin 3) x,fderiv ℝ f x (EuclideanSpace.single (Fin.natAdd 1 a.1,a.2) 1)=0)
    (hperm:∀ (p:Equiv.Perm (Fin k)) x,f (permute (corePerm 1 p) x)=f x)
    (hkin:let z:=u.smoothMul f hf B D hB hD
      let v:=z.smoothMul f hf B D hB hD
      0≤∑ s,∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x)) :
    let z:=u.smoothMul f hf B D hB hD
    potentialForm (fun x => crossPotential ((joinConfiguration 1 k).symm x).1
      ((joinConfiguration 1 k).symm x).2) z ≤
      potentialForm (fun x => nuclearPotential (atom Z hZ) ((joinConfiguration 1 k).symm x).1) z := by
  let z:=u.smoothMul f hf B D hB hD
  let v:=z.smoothMul f hf B D hB hD
  have hi(s:Spins (1+k))(x:Configuration (1+k)):
      inner ℝ (u.value s x) (v.value s x)=‖z.value s x‖^2:=inner_double_real _ _
  have hmz:massPair u v=mass z := by simp only [massPair,mass,hi]
  have hnz:nuclearPair (atom Z hZ) u v=nuclearEnergy (atom Z hZ) z := by
    simp only [nuclearPair,nuclearEnergy,hi]
  have hpz:repulsionPair u v=pairEnergy z := by simp only [repulsionPair,pairEnergy,hi,pairPotential]
  have hg(s:Spins (1+k))(a:Fin k × Fin 3)(x:Configuration (1+k)):
      inner ℝ (u.gradient s (Fin.natAdd 1 a.1,a.2) x)
        (v.gradient s (Fin.natAdd 1 a.1,a.2) x)=
        ‖z.gradient s (Fin.natAdd 1 a.1,a.2) x‖^2 := by
    simp only [v,z,H1Vector.smoothMul,hcore,Complex.ofReal_zero,zero_mul,zero_add]
    exact inner_double_real _ _
  have hk:kineticPair u v=coreKinetic z+
      (1/2:ℝ)*(∑ s,∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x)) := by
    unfold kineticPair coreKinetic
    simp only [Fintype.sum_prod_type,Fin.sum_univ_add,Fin.sum_univ_one,Finset.sum_add_distrib]
    have hg' (s:Spins (1+k))(i:Fin k)(a:Fin 3)(x:Configuration (1+k)) := hg s (i,a) x
    simp only [hg',show Fin.castAdd k (0:Fin 1)=(0:Fin (1+k)) from rfl]
    ring
  have he:=sector_minimizer_ambient_eigen Z hZ u ha hm hmin v
  rw [formPair,hk,hnz,hpz,hmz] at he
  have hanti:∀ s:Spins 1,∀ᵐ x,Antisymmetric (z.coreSlice s x) := by
    intro s
    apply z.coreSlice_antisymmetric
    intro p t
    filter_upwards [ha (corePerm 1 p) (Fin.append s t)] with x hx
    change (f (permute (corePerm 1 p) x):ℂ)*u.value _ (permute (corePerm 1 p) x)=_
    rw [hperm,hx]
    change (f x:ℂ)*(_*u.value _ x)=_ *((f x:ℂ)*u.value _ x)
    ring
  have hs:=slice_core_form_ge_sector (atom Z hZ) z hanti
    (P:=form (atom Z hZ) u)
    (hmin.le.trans (atom_sectorFormBottom_antitone Z hZ (by omega : k≤1+k)))
  change _≤∑ s:Spins 1,∫ x,mass (z.coreSlice s x)*form (atom Z hZ) (z.coreSlice s x).normalized at hs
  rw [conditional_core_form_identity] at hs
  rw [nuclearEnergy_split,pairEnergy_split] at he
  have houter:0≤potentialForm (fun x => pairPotential ((joinConfiguration 1 k).symm x).1) z := by
    apply Finset.sum_nonneg
    intro s _
    exact integral_nonneg fun x => mul_nonneg (by
      unfold pairPotential
      apply Finset.sum_nonneg
      intro i _
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact inv_nonneg.mpr (norm_nonneg _)
      · rfl) (sq_nonneg _)
  dsimp only at hkin ⊢
  change _≤_
  linarith only [he,hs,houter,hkin]
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicWeighted
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma potentialForm_smoothMul {n:ℕ} (u:H1Vector n) (f:SmoothBoundedCoefficient) (i:Fin n)
    (V:Configuration n → ℝ):
    potentialForm V (u.smoothMul (fun x => f.value (position x i)) (f.lift_smooth i)
      f.bound f.derivBound (fun x => f.value_le (position x i)) (f.lift_deriv_le i))=
    potentialForm (fun x => V x*(f.value (position x i))^2) u := by
  unfold potentialForm
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [] with x
  simp only [H1Vector.smoothMul,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  ring
lemma regularized_weighted_core (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    (l e:ℝ) (hl:l≠0) (he:0<e):
    potentialForm (fun x => (∑ j:Fin k,coulombKernel (position x 0-position x (Fin.natAdd 1 j)))*
      (regularizedU l e (position x 0))⁻¹) u ≤
    potentialForm (fun x => (Z:ℝ)*coulombKernel (position x 0)*
      (regularizedU l e (position x 0))⁻¹) u := by
  let f:=rootReciprocalCoefficient l e hl he
  let w:=reciprocalCoefficient l e hl he
  let z:=u.smoothMul (fun x => f.value (position x 0)) (f.lift_smooth 0) f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  let v:=z.smoothMul (fun x => f.value (position x 0)) (f.lift_smooth 0) f.bound f.derivBound
    (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0)
  let v':=u.smoothMul (fun x => w.value (position x 0)) (w.lift_smooth 0) w.bound w.derivBound
    (fun x => w.value_le (position x 0)) (w.lift_deriv_le 0)
  have hv:∀ s,v.value s =ᵐ[volume] v'.value s := by
    intro s
    filter_upwards [] with x
    change (f.value (position x 0):ℂ)*((f.value (position x 0):ℂ)*u.value s x)=
      (w.value (position x 0):ℂ)*u.value s x
    rw [←mul_assoc,←sq,←Complex.ofReal_pow,rootReciprocalCoefficient_sq]
  have hk:0≤∑ s,∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x) := by
    apply Finset.sum_nonneg
    intro s _
    have H:=regularized_weight_kinetic u s l e hl he
    change 0≤∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v'.gradient s (0,a) x) at H
    have Heq:(∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v.gradient s (0,a) x))=
        ∑ a:Fin 3,∫ x,inner ℝ (u.gradient s (0,a) x) (v'.gradient s (0,a) x) := by
      apply Finset.sum_congr rfl
      intro a _
      exact integral_congr_ae ((v.gradient_congr_ae v' hv s (0,a)).mono (fun x hx => by dsimp only; rw [hx]))
    rw [Heq]
    exact H
  have hc:∀ (a:Fin k × Fin 3) x,fderiv ℝ (fun y => f.value (position y 0)) x
      (EuclideanSpace.single (Fin.natAdd 1 a.1,a.2) 1)=0 := by
    intro a x
    rw [oneBody_derivative f.value f.smooth]
    exact ite_eq_right (by intro H; have hh:=congrArg Fin.val H; simp only [Fin.val_zero,Fin.val_natAdd] at hh; omega)
  have hp:∀ (p:Equiv.Perm (Fin k)) x,f.value (position (permute (corePerm 1 p) x) 0)=f.value (position x 0) := by
    intro p x
    rw [position_permute]
    have H:=corePerm_left 1 p (0:Fin 1)
    change corePerm 1 p 0=0 at H
    rw [H]
  have H:=weighted_core_inequality Z hZ u ha hm hmin _ (f.lift_smooth 0)
    f.bound f.derivBound (fun x => f.value_le (position x 0)) (f.lift_deriv_le 0) hc hp hk
  dsimp only at H
  rw [potentialForm_smoothMul,potentialForm_smoothMul] at H
  simp only [f,rootReciprocalCoefficient_sq,reciprocalCoefficient,crossPotential,
    Fin.sum_univ_one,position_split_left,position_split_right,nuclearPotential,attraction,atom,
    show Fin.castAdd k (0:Fin 1)=(0:Fin (1+k)) from rfl,sub_zero] at H
  exact H
end Coulomb
end

end
section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace Coulomb
lemma atomicCross_integrable {k:ℕ} (u:H1Vector (1+k)) (s:Spins (1+k)):
    Integrable (fun x => atomicCross x*‖u.value s x‖^2) := by
  simpa only [crossPotential,Fin.sum_univ_one,position_split_left,position_split_right,
    show Fin.castAdd k (0:Fin 1)=(0:Fin (1+k)) from rfl,atomicCross] using u.cross_integrable (m:=1) (k:=k) s
lemma potentialForm_bdd_mul_integrable {n:ℕ} (u:H1Vector n) (V f:Configuration n → ℝ)
    (hV:∀ s,Integrable (fun x => V x*‖u.value s x‖^2))
    (hf:AEStronglyMeasurable f volume) {C:ℝ} (hC:∀ᵐ x,‖f x‖≤C) (s:Spins n):
    Integrable (fun x => V x*f x*‖u.value s x‖^2) := by
  exact ((hV s).mul_bdd hf hC).congr (Eventually.of_forall (fun x => by dsimp only; ring))
lemma potentialForm_tendsto_bdd {n:ℕ} (u:H1Vector n) (V:Configuration n → ℝ)
    (hV:∀ s,Integrable (fun x => V x*‖u.value s x‖^2))
    (f:ℕ → Configuration n → ℝ) (g:Configuration n → ℝ) (C:ℝ)
    (hf:∀ j,AEStronglyMeasurable (f j) volume) (hC:∀ j,∀ᵐ x,‖f j x‖≤C)
    (ht:∀ᵐ x,Tendsto (fun j => f j x) atTop (𝓝 (g x))):
    Tendsto (fun j => potentialForm (fun x => V x*f j x) u) atTop
      (𝓝 (potentialForm (fun x => V x*g x) u)) := by
  unfold potentialForm
  apply tendsto_finsetSum
  intro s _
  apply tendsto_integral_of_dominated_convergence (fun x => ‖V x*‖u.value s x‖^2‖*C)
  · intro j
    exact (potentialForm_bdd_mul_integrable u V (f j) hV (hf j) (hC j) s).aestronglyMeasurable
  · exact (hV s).norm.mul_const C
  · intro j
    filter_upwards [hC j] with x hx
    rw [show V x*f j x*‖u.value s x‖^2=(V x*‖u.value s x‖^2)*f j x by ring,norm_mul]
    exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
  · filter_upwards [ht] with x hx
    exact (tendsto_const_nhds.mul hx).mul_const _

lemma atomicWeight_bound {e:ℝ} (he:0<e) (x:Space):‖atomicWeight e x‖≤e⁻¹ := by
  rw [Real.norm_eq_abs,abs_of_nonneg (by unfold atomicWeight coulombKernel; positivity)]
  exact inv_anti₀ he (by change e≤‖x‖⁻¹+e; exact le_add_of_nonneg_left (inv_nonneg.mpr (norm_nonneg x)))
lemma atomicWeight_measurable (e:ℝ):Measurable (atomicWeight e) :=
  (coulombKernel_measurable.add_const e).inv
lemma regularized_weighted_core_limit (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    (e:ℝ) (he:0<e):
    potentialForm (fun x => atomicCross x*atomicWeight e (position x 0)) u ≤
    potentialForm (fun x => (Z:ℝ)*coulombKernel (position x 0)*atomicWeight e (position x 0)) u := by
  let l:ℕ → ℝ:=fun j => ((j:ℝ)+1)⁻¹
  have hl:∀ j,l j≠0:=fun j => ne_of_gt (by dsimp [l]; positivity)
  have ht:Tendsto l atTop (𝓝 0):=by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  let f:ℕ → Configuration (1+k) → ℝ:=fun j x => (regularizedU (l j) e (position x 0))⁻¹
  have hf:∀ j,AEStronglyMeasurable (f j) volume:=fun j =>
    ((reciprocalCoefficient (l j) e (hl j) he).lift_smooth (0:Fin (1+k))).continuous.aestronglyMeasurable
  have hb:∀ j,∀ᵐ x,‖f j x‖≤e⁻¹ := by
    intro j
    exact Eventually.of_forall (fun x => by simpa only [f,reciprocalCoefficient,Real.norm_eq_abs] using
      (reciprocalCoefficient (l j) e (hl j) he).value_le (position x 0))
  have hft:∀ᵐ x:Configuration (1+k),Tendsto (fun j => f j x) atTop (𝓝 (atomicWeight e (position x 0))) := by
    filter_upwards [ae_position_ne (1+k) 0] with x hx
    exact ((NeutralAtom.regularizedKernel_tendsto ht (hx 0)).add_const e).inv₀
      (by change (‖position x 0‖⁻¹+e)≠0; positivity)
  have hleft:=potentialForm_tendsto_bdd u atomicCross (atomicCross_integrable u) f _ _ hf hb hft
  have hv:∀ s,Integrable (fun x:Configuration (1+k) => (Z:ℝ)*coulombKernel (position x 0)*‖u.value s x‖^2) := by
    intro s
    simpa only [sub_zero,mul_assoc] using
      ((u.nuclear_coulomb_integrable_bound s 0 (0:Space) (by norm_num : (0:ℝ)<1)).1.const_mul (Z:ℝ))
  have hright:=potentialForm_tendsto_bdd u (fun x => (Z:ℝ)*coulombKernel (position x 0)) hv f _ _ hf hb hft
  exact le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall fun j =>
    regularized_weighted_core Z hZ u ha hm hmin (l j) e (hl j) he)
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_FieldAnalysis_AtomicWeightGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma atomicFraction_nonneg {e:ℝ} (he:0<e) (x:Space):0≤atomicFraction e x := by
  unfold atomicFraction atomicWeight coulombKernel
  positivity
lemma atomicFraction_le_one {e:ℝ} (he:0<e) (x:Space):atomicFraction e x≤1 := by
  change ‖x‖⁻¹*(‖x‖⁻¹+e)⁻¹≤1
  rw [←div_eq_mul_inv,div_le_one (by positivity)]
  linarith
lemma atomicFraction_measurable (e:ℝ):Measurable (atomicFraction e) :=
  coulombKernel_measurable.mul (atomicWeight_measurable e)
lemma atomicWeight_eq_radius {e:ℝ} (he:0<e) {x:Space} (hx:x≠0):
    atomicWeight e x=‖x‖/(1+e*‖x‖) := by
  unfold atomicWeight coulombKernel
  have hr:=norm_pos_iff.mpr hx
  field_simp
lemma atomicFraction_eq_radius {e:ℝ} (he:0<e) {x:Space} (hx:x≠0):
    atomicFraction e x=1/(1+e*‖x‖) := by
  rw [atomicFraction,atomicWeight_eq_radius he hx]
  unfold coulombKernel
  field_simp
lemma atomic_weight_triangle {e:ℝ} (he:0<e) {x y:Space} (hx:x≠0) (hy:y≠0) (hxy:x≠y):
    atomicFraction e x*atomicFraction e y ≤ coulombKernel (x-y)*(atomicWeight e x+atomicWeight e y) := by
  rw [atomicFraction_eq_radius he hx,atomicFraction_eq_radius he hy,
    atomicWeight_eq_radius he hx,atomicWeight_eq_radius he hy]
  let a:=1+e*‖x‖
  let b:=1+e*‖y‖
  have ha:0<a:=by dsimp [a]; positivity
  have hb:0<b:=by dsimp [b]; positivity
  have hd:0<‖x-y‖:=norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hn:‖x-y‖≤‖x‖*b+‖y‖*a := by
    have H:=norm_sub_le x y
    have H0:0≤e*‖x‖*‖y‖:=by positivity
    dsimp [a,b]
    nlinarith
  change 1/a*(1/b)≤‖x-y‖⁻¹*(‖x‖/a+‖y‖/b)
  calc
    _=‖x-y‖/(‖x-y‖*(a*b)):=by field_simp
    _≤(‖x‖*b+‖y‖*a)/(‖x-y‖*(a*b)):=div_le_div_of_nonneg_right hn (by positivity)
    _= _:=by field_simp
lemma potentialForm_finsetSum {n:ℕ} {ι:Type*} (u:H1Vector n) (A:Finset ι)
    (f:ι → Configuration n → ℝ)
    (hi:∀ i∈A,∀ s,Integrable (fun x => f i x*‖u.value s x‖^2)):
    potentialForm (fun x => ∑ i∈A,f i x) u=∑ i∈A,potentialForm (f i) u := by
  unfold potentialForm
  simp only [Finset.sum_mul]
  simp_rw [integral_finsetSum A (fun i hi' => hi i hi' _)]
  exact Finset.sum_comm
lemma potentialForm_add {n:ℕ} (u:H1Vector n) (f g:Configuration n → ℝ)
    (hf:∀ s,Integrable (fun x => f x*‖u.value s x‖^2))
    (hg:∀ s,Integrable (fun x => g x*‖u.value s x‖^2)):
    potentialForm (fun x => f x+g x) u=potentialForm f u+potentialForm g u := by
  unfold potentialForm
  simp only [add_mul,integral_add (hf _) (hg _),Finset.sum_add_distrib]
lemma potentialForm_mono_ae {n:ℕ} (u:H1Vector n) (f g:Configuration n → ℝ)
    (hf:∀ s,Integrable (fun x => f x*‖u.value s x‖^2))
    (hg:∀ s,Integrable (fun x => g x*‖u.value s x‖^2)) (h:∀ᵐ x,f x≤g x):
    potentialForm f u≤potentialForm g u := by
  exact Finset.sum_le_sum (fun s _ => integral_mono_ae (hf s) (hg s)
    (h.mono fun x hx => mul_le_mul_of_nonneg_right hx (sq_nonneg _)))
lemma pair_weight_integrable {n:ℕ} (u:H1Vector n) (i j a:Fin n) (hij:i≠j)
    {e:ℝ} (he:0<e) (s:Spins n):
    Integrable (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x a)*‖u.value s x‖^2) :=
  potentialForm_bdd_mul_integrable u _ _ (fun s =>
    (u.pair_coulomb_integrable_bound s i j hij (by norm_num : (0:ℝ)<1)).1)
    (((atomicWeight_measurable e).comp (continuous_position a).measurable).aestronglyMeasurable)
    (Eventually.of_forall (fun x => atomicWeight_bound he (position x a))) s
lemma pair_weight_symmetry {n:ℕ} (u:H1Vector n) (ha:Antisymmetric u) (i j:Fin n) (e:ℝ):
    potentialForm (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x j)) u=
    potentialForm (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x i)) u := by
  have H:=antisymmetric_expectation_permute ha (Equiv.swap i j)
    (fun x => coulombKernel (position x i-position x j)*atomicWeight e (position x i))
  simpa only [potentialForm,position_permute,Equiv.swap_apply_left,Equiv.swap_apply_right,coulombKernel,norm_sub_rev] using H
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_Screening_AtomicNumber
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma bounded_potential_integrable {n:ℕ} (u:H1Vector n) (f:Configuration n → ℝ)
    (hf:AEStronglyMeasurable f volume) {C:ℝ} (hb:∀ᵐ x,‖f x‖≤C) (s:Spins n):
    Integrable (fun x => f x*‖u.value s x‖^2) :=
  (u.value_L2 s).norm.integrable_sq.bdd_mul hf hb
lemma fraction_pair_integrable {n:ℕ} (u:H1Vector n) (i j:Fin n) {e:ℝ} (he:0<e) (s:Spins n):
    Integrable (fun x => atomicFraction e (position x i)*atomicFraction e (position x j)*‖u.value s x‖^2) := by
  apply bounded_potential_integrable u _
    ((((atomicFraction_measurable e).comp (continuous_position i).measurable).mul
      ((atomicFraction_measurable e).comp (continuous_position j).measurable)).aestronglyMeasurable)
    (C:=1) _ s
  exact Eventually.of_forall fun x => by
    dsimp only [Function.comp_apply,Pi.mul_apply]
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (atomicFraction_nonneg he _) (atomicFraction_nonneg he _))]
    exact (mul_le_of_le_one_left (atomicFraction_nonneg he _)
      (atomicFraction_le_one he _)).trans (atomicFraction_le_one he _)
lemma weighted_attraction_le {n:ℕ} (Z:ℕ) (u:H1Vector n) (hm:mass u=1) (i:Fin n)
    {e:ℝ} (he:0<e):
    potentialForm (fun x => (Z:ℝ)*coulombKernel (position x i)*atomicWeight e (position x i)) u≤Z := by
  have hi:∀ s,Integrable (fun x => (Z:ℝ)*atomicFraction e (position x i)*‖u.value s x‖^2) := by
    intro s
    apply bounded_potential_integrable u _
      (((atomicFraction_measurable e).comp (continuous_position i).measurable).const_mul (Z:ℝ)).aestronglyMeasurable
      (C:=(Z:ℝ)) _ s
    exact Eventually.of_forall fun x => by
      dsimp only [Function.comp_apply,Pi.mul_apply]
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (atomicFraction_nonneg he _))]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) (atomicFraction_le_one he _)
  have H:=potentialForm_mono_ae u (fun x => (Z:ℝ)*atomicFraction e (position x i)) (fun _ => (Z:ℝ)) hi
    (fun s => (u.value_L2 s).norm.integrable_sq.const_mul _) (Eventually.of_forall fun x =>
      mul_le_of_le_one_right (Nat.cast_nonneg _) (atomicFraction_le_one he _))
  rw [potentialForm_const,hm,mul_one] at H
  simpa only [atomicFraction,mul_assoc] using H
lemma atomic_fraction_pair_bound (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k))
    {e:ℝ} (he:0<e):
    (∑ j:Fin k,potentialForm (fun x => atomicFraction e (position x 0)*
      atomicFraction e (position x (Fin.natAdd 1 j))) u)≤2*(Z:ℝ) := by
  have hne(j:Fin k):(0:Fin (1+k))≠Fin.natAdd 1 j:=by
    intro hh; have H:=congrArg Fin.val hh; simp only [Fin.val_zero,Fin.val_natAdd] at H; omega
  let F:Fin k → Configuration (1+k) → ℝ:=fun j x =>
    coulombKernel (position x 0-position x (Fin.natAdd 1 j))*atomicWeight e (position x 0)
  have hi:∀ j:Fin k,∀ s,Integrable (fun x => F j x*‖u.value s x‖^2):=fun j s =>
    pair_weight_integrable u 0 (Fin.natAdd 1 j) 0 (hne j) he s
  have hj(j:Fin k):potentialForm (fun x => atomicFraction e (position x 0)*
      atomicFraction e (position x (Fin.natAdd 1 j))) u≤2*potentialForm (F j) u := by
    have hi':∀ s,Integrable (fun x => coulombKernel (position x 0-position x (Fin.natAdd 1 j))*
        atomicWeight e (position x (Fin.natAdd 1 j))*‖u.value s x‖^2):=fun s =>
      pair_weight_integrable u 0 (Fin.natAdd 1 j) (Fin.natAdd 1 j) (hne j) he s
    have H:=potentialForm_mono_ae u _
      (fun x => F j x+coulombKernel (position x 0-position x (Fin.natAdd 1 j))*atomicWeight e (position x (Fin.natAdd 1 j)))
      (fraction_pair_integrable u 0 (Fin.natAdd 1 j) he)
      (fun s => ((hi j s).add (hi' s)).congr (Eventually.of_forall fun x => by dsimp only; rw [add_mul]; rfl)) (by
        filter_upwards [ae_position_ne (1+k) 0,ae_position_injective (1+k)] with x hx hp
        simpa only [F,mul_add] using atomic_weight_triangle he (hx 0) (hx (Fin.natAdd 1 j))
          (fun h => hne j (hp h)))
    rw [potentialForm_add _ _ _ (hi j) hi',pair_weight_symmetry u ha] at H
    linarith only [H]
  have Hsum:=Finset.sum_le_sum (fun j (_:j∈(Finset.univ:Finset (Fin k))) => hj j)
  rw [←Finset.mul_sum,←potentialForm_finsetSum u Finset.univ F (fun j _ => hi j)] at Hsum
  have hid:(fun x => ∑ j:Fin k,F j x)=(fun x => atomicCross x*atomicWeight e (position x 0)):=by
    funext x; simp only [F,atomicCross,Finset.sum_mul]
  rw [hid] at Hsum
  exact Hsum.trans (mul_le_mul_of_nonneg_left
    ((regularized_weighted_core_limit Z hZ u ha hm hmin e he).trans (weighted_attraction_le Z u hm 0 he)) (by norm_num))
lemma atomicFraction_tendsto {e:ℕ → ℝ} (ht:Tendsto e atTop (𝓝 0)) {x:Space} (hx:x≠0):
    Tendsto (fun j => atomicFraction (e j) x) atTop (𝓝 1) := by
  have hr:0 < coulombKernel x:=inv_pos.mpr (norm_pos_iff.mpr hx)
  have H:=(tendsto_const_nhds (x:=coulombKernel x)).mul ((tendsto_const_nhds.add ht).inv₀ (by simpa using hr.ne'))
  simpa only [atomicFraction,atomicWeight,add_zero,mul_inv_cancel₀ hr.ne'] using H
lemma atom_minimizer_number_bound (Z:ℕ) (hZ:1≤Z) {k:ℕ}
    (u:H1Vector (1+k)) (ha:Antisymmetric u) (hm:mass u=1)
    (hmin:(form (atom Z hZ) u:EReal)=sectorFormBottom (atom Z hZ) (1+k)):
    k≤2*Z := by
  let e:ℕ → ℝ:=fun j => ((j:ℝ)+1)⁻¹
  have he:∀ j,0<e j:=fun j => by dsimp [e]; positivity
  have ht:Tendsto e atTop (𝓝 0):=by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)
  have hlim(j:Fin k):Tendsto (fun q => potentialForm (fun x => atomicFraction (e q) (position x 0)*
      atomicFraction (e q) (position x (Fin.natAdd 1 j))) u) atTop (𝓝 1) := by
    have H:=potentialForm_tendsto_bdd u (fun _ => 1)
      (fun s => by simpa using (u.value_L2 s).norm.integrable_sq)
      (fun q x => atomicFraction (e q) (position x 0)*atomicFraction (e q) (position x (Fin.natAdd 1 j)))
      (fun _ => 1) 1
      (fun q => by
        apply AEStronglyMeasurable.mul
        · exact ((atomicFraction_measurable (e q)).comp (continuous_position 0).measurable).aestronglyMeasurable
        · exact ((atomicFraction_measurable (e q)).comp (continuous_position (Fin.natAdd 1 j)).measurable).aestronglyMeasurable)
      (fun q => Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (atomicFraction_nonneg (he q) _) (atomicFraction_nonneg (he q) _))]
        exact (mul_le_of_le_one_left (atomicFraction_nonneg (he q) _)
          (atomicFraction_le_one (he q) _)).trans (atomicFraction_le_one (he q) _))
      (by
        filter_upwards [ae_position_ne (1+k) 0] with x hx
        simpa only [one_mul] using (atomicFraction_tendsto ht (hx 0)).mul
          (atomicFraction_tendsto ht (hx (Fin.natAdd 1 j))))
    simpa only [one_mul,potentialForm_const,hm,mul_one] using H
  have Hlim:=tendsto_finsetSum Finset.univ (fun j _ => hlim j)
  have H:=le_of_tendsto Hlim (Eventually.of_forall fun q => atomic_fraction_pair_bound Z hZ u ha hm hmin (he q))
  have H':(k:ℝ)≤2*(Z:ℝ):=by simpa using H
  exact_mod_cast H'
end Coulomb
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_StrictBinding
attribute [-instance] _root_.OAI.NeutralAtom.observationLaw_probability _root_.OAI.NeutralAtom.observationSample_standardBorel
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical ContDiff
noncomputable section
namespace NeutralAtom
lemma integral_first_weighted_tensor {n:ℕ} (f:Position → ℝ) (ψ:Configuration n → ℂ) (W:Position → ℝ):
    (∫ x:Configuration (n+1),W (x 0)*‖f (x 0) • ψ (fun i => x i.succ)‖^2)=
    (∫ y:Position,W y*(f y)^2)*(∫ x:Configuration n,‖ψ x‖^2) := by
  have he := (configurationSplit_preserving n).integral_comp
    (configurationSplit n).toHomeomorph.measurableEmbedding
    (fun z:Position × Configuration n => (W z.1*(f z.1)^2)*‖ψ z.2‖^2)
  rw [←integral_prod_mul (μ:=volume) (ν:=volume) (fun y:Position => W y*(f y)^2)
    (fun x:Configuration n => ‖ψ x‖^2)]
  change _ = ∫ z:Position × Configuration n,(W z.1*(f z.1)^2)*‖ψ z.2‖^2
  rw [←he]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [configurationSplit_apply,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    ring
lemma weighted_normSquared_insert_first {n:ℕ} (f:Position → ℝ) (ψ:Wavefunction n) (W:Position → ℝ):
    (∑ s:Spins (n+1),∫ x,W (x 0)*‖insertWavefunction f ψ s x‖^2)=
    (∫ y:Position,W y*(f y)^2)*normSquared ψ := by
  rw [←Equiv.sum_comp (Fin.consEquiv (fun _:Fin (n+1) => Fin 2))]
  rw [Fintype.sum_prod_type,Fin.sum_univ_two]
  have h10:(1:Fin 2)≠0:=by decide
  simp only [Fin.consEquiv,Equiv.coe_fn_mk,insertWavefunction,Fin.cons_zero,
    Fin.cons_succ,h10,↓reduceIte,norm_zero,zero_pow (by decide : 2≠0),mul_zero,
    integral_zero,Finset.sum_const_zero,add_zero,integral_first_weighted_tensor,Finset.mul_sum,normSquared]
lemma distantPacket_outer_zero {t:ℝ} (ht:0<t) {y:Position} (hy:6*t≤‖y‖):distantPacket t y=0 := by
  have hnorm:6≤‖t⁻¹ • y‖ := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht)]
    exact (le_inv_mul_iff₀ ht).mpr (by linarith)
  have hdist:2≤‖t⁻¹ • y-distantCenter‖ := by
    have H:=norm_sub_norm_le (t⁻¹ • y) distantCenter
    rw [distantCenter_norm] at H
    linarith
  have H:=bindingBump.zero_of_le_dist (by simpa [bindingBump] using hdist)
  simp [distantPacket,H]
lemma distantPacket_attraction {t:ℝ} (ht:0<t):
    (6*t)⁻¹≤∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2 := by
  have hi:Integrable (fun y:Position => ‖y‖⁻¹*(distantPacket t y)^2) := by
    exact locallyIntegrable_coulombKernel.integrable_smul_right_of_hasCompactSupport
      ((distantPacket_smooth t).continuous.pow 2) (by
        simp only [sq]
        change HasCompactSupport ((distantPacket t)*(distantPacket t))
        exact (distantPacket_compact ht).mul_left)
  have hi':Integrable (fun y:Position => (6*t)⁻¹*(distantPacket t y)^2):=
    ((distantPacket_memLp ht).integrable_sq).const_mul _
  have H:=integral_mono hi' hi (fun y => by
    by_cases hz:distantPacket t y=0
    · simp [hz]
    · have hy:‖y‖<6*t:=lt_of_not_ge (fun h => hz (distantPacket_outer_zero ht h))
      have hy0:0<‖y‖:=lt_of_le_of_lt (by positivity : (0:ℝ)≤2*t)
        (lt_of_not_ge (fun h => hz (distantPacket_zero ht h)))
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hy0 hy.le) (sq_nonneg _))
  rwa [integral_const_mul,distantPacket_normalized ht,mul_one] at H
lemma onePacket_domain {t:ℝ} (ht:0<t):
    FormDomain (insertWavefunction (distantPacket t) vacuumWavefunction)
      (insertGradient (distantPacket t) vacuumWavefunction vacuumGradient) := by
  refine ⟨?_,FormRegular.insert_separated vacuum_formDomain.2 ht ht (R:=0) ?_
    (distantPacket_smooth t) (distantPacket_memLp ht) (fun a => distantPacket_derivative_memLp ht _) ?_⟩
  · intro p s
    have hp:p=1:=by
      apply Equiv.ext
      intro i
      apply Fin.ext
      change (p i).val=i.val
      have H1:(p i).val<1:=(p i).isLt
      have H2:i.val<1:=i.isLt
      omega
    subst p
    simp
  · intro s x hx
    have H:x=0:=Subsingleton.elim _ _
    simp [H] at hx
  · intro y hy
    exact distantPacket_zero ht (by linarith)
lemma onePacket_energy (Z:ℕ) {t:ℝ} (ht:0<t):
    energy Z (insertWavefunction (distantPacket t) vacuumWavefunction)
      (insertGradient (distantPacket t) vacuumWavefunction vacuumGradient)=
    (1/2:ℝ)*t⁻¹^2*(distantMass⁻¹*oneParticleGradientNorm bindingBump)-
      (Z:ℝ)*(∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2) := by
  rw [energy_decompose,gradientNormSquared_insert,vacuum_normalized,distantPacket_gradientNorm ht]
  have hp:potentialForm Z (insertWavefunction (distantPacket t) vacuumWavefunction)=
      -(Z:ℝ)*(∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2) := by
    unfold potentialForm
    have hV:∀ x:Configuration 1,coulombPotential Z x= -(Z:ℝ)*‖x 0‖⁻¹ := by
      intro x
      simp [coulombPotential,Finset.filter_singleton]
    simp_rw [hV,neg_mul,mul_assoc,integral_neg,integral_const_mul]
    rw [Finset.sum_neg_distrib,←Finset.mul_sum]
    have hw:=weighted_normSquared_insert_first (distantPacket t) vacuumWavefunction (fun y:Position => ‖y‖⁻¹)
    rw [hw,vacuum_normalized,mul_one]
  rw [hp]
  simp only [gradientNormSquared,Finset.univ_eq_empty,Finset.sum_empty,mul_zero,zero_add,mul_one]
  ring
lemma sectorEnergy_one_neg (Z:ℕ) (hZ:1≤Z):sectorEnergy Z 1<0 := by
  let C:=distantMass⁻¹*oneParticleGradientNorm bindingBump
  let t:ℝ:=3*|C|+1
  have ht:0<t:=by dsimp [t]; positivity
  have hnorm:normSquared (insertWavefunction (distantPacket t) vacuumWavefunction)=1:=by
    rw [normSquared_insert,distantPacket_normalized ht,vacuum_normalized,mul_one]
  have H:=sectorEnergy_le_trial (Z:=Z) (onePacket_domain ht) hnorm
  apply lt_of_le_of_lt H
  rw [onePacket_energy Z ht]
  apply EReal.coe_lt_coe_iff.mpr
  have hZ':(1:ℝ)≤Z:=by exact_mod_cast hZ
  have ha:=distantPacket_attraction ht
  have hb:(6*t)⁻¹≤(Z:ℝ)*(∫ y:Position,‖y‖⁻¹*(distantPacket t y)^2):=
    ha.trans (le_mul_of_one_le_left (le_trans (by positivity) ha) hZ')
  have hsmall:(1/2:ℝ)*t⁻¹^2*C<(6*t)⁻¹ := by
    have hc:C≤|C|:=le_abs_self C
    have ht3:3*C<t:=by dsimp [t]; linarith
    apply (mul_lt_mul_iff_left₀ (show 0<6*t^2 by positivity)).mp
    field_simp
    nlinarith
  change (1/2:ℝ)*t⁻¹^2*C-(Z:ℝ)*_ < 0
  linarith
end NeutralAtom
end

end

end OAI
end

section
-- module Solutions.OAIQ062_CR.CoulombRadii_SpectralTheory_GlobalSectorMinimum
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Classical
noncomputable section
namespace Coulomb
lemma atom_strict_sector_bound (Z:ℕ) (hZ:1≤Z) {n:ℕ} (hn:0<n)
    (h:sectorFormBottom (atom Z hZ) n < sectorFormBottom (atom Z hZ) (n-1)):
    n≤3*Z := by
  obtain ⟨k,rfl⟩:=Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 k] at h ⊢
  rw [Nat.add_comm k 1] at h ⊢
  obtain ⟨u,ha,hm,he⟩:=atom_strict_binding_attained Z hZ (by omega : 0<1+k) h
  have H:=atom_minimizer_number_bound Z hZ u ha hm he
  omega
lemma atom_global_sector_minimum_oai (Z:ℕ) (hZ:1≤Z):
    ∃ n:ℕ,0<n ∧ n≤3*Z ∧ ∃ u:H1Vector n,Antisymmetric u ∧ mass u=1 ∧
      (form (atom Z hZ) u:EReal)=unrestrictedFormBottom (atom Z hZ) := by
  let E:ℕ → EReal:=sectorFormBottom (atom Z hZ)
  let A:= (Finset.range (3*Z+1)).filter (fun n => 0<n ∧ E n<E (n-1))
  have h1:E 1<E 0 := by
    dsimp [E]
    rw [←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,←NeutralAtom.sectorEnergy_eq_formBottom Z hZ,
      NeutralAtom.sectorEnergy_vacuum]
    exact NeutralAtom.sectorEnergy_one_neg Z hZ
  have hA:A.Nonempty := by
    refine ⟨1,?_⟩
    rw [Finset.mem_filter,Finset.mem_range]
    exact ⟨by omega,by norm_num; exact h1⟩
  let N:=A.max' hA
  have hN:N∈A:=Finset.max'_mem A hA
  have hn:0<N ∧ E N<E (N-1):=(Finset.mem_filter.mp hN).2
  have hNb:N≤3*Z:=by have H: N<3*Z+1:=Finset.mem_range.mp (Finset.mem_filter.mp hN).1; omega
  have hmax:∀ n,0<n → E n<E (n-1) → n≤N := by
    intro n hn hs
    apply Finset.le_max'
    rw [Finset.mem_filter,Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le (atom_strict_sector_bound Z hZ hn hs),hn,hs⟩
  have hplateau:∀ d,E (N+d)=E N := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
      have hle:E (N+(d+1))≤E (N+d):=atom_sectorFormBottom_antitone Z hZ (by omega)
      have hnlt:¬E (N+(d+1))<E (N+d) := by
        intro H
        have hh:=hmax (N+(d+1)) (by omega) (by simpa using H)
        omega
      exact (le_antisymm hle (le_of_not_gt hnlt)).trans ih
  have hglobal:E N=unrestrictedFormBottom (atom Z hZ) := by
    apply le_antisymm
    · apply le_iInf
      intro n
      by_cases hn:n≤N
      · exact atom_sectorFormBottom_antitone Z hZ hn
      · obtain ⟨d,rfl⟩:=Nat.exists_eq_add_of_le (le_of_not_ge hn)
        exact (hplateau d).ge
    · exact iInf_le E N
  obtain ⟨u,ha,hm,he⟩:=atom_strict_binding_attained Z hZ hn.1 hn.2
  exact ⟨N,hn.1,hNb,u,ha,hm,he.trans hglobal⟩
end Coulomb
end

end

end OAI
end

theorem solution : type_of% @OAI.Coulomb.atom_global_sector_minimum_oai := @OAI.Coulomb.atom_global_sector_minimum_oai
