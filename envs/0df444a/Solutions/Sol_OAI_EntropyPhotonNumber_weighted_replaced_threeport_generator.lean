-- Prove2me | solution 1 for OAI.EntropyPhotonNumber.weighted_replaced_threeport_generator
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T04:51:55.258985+00:00
-- url     : https://prove2.me/submissions/4010b22f-3a5f-42bc-afe8-fccf615aefd9

-- Generated from openai/math@1581d4c lean/OAI/InformationTheory/PhotonNumber/Generator.lean:L343-L373
-- (upload_full_project.md Phase 4): solution for node OAI.EntropyPhotonNumber.weighted_replaced_threeport_generator. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Theorems.Thm_OAI_Annihilation_weighted_trace_ext
import Theorems.Thm_OAI_BeamLadder_weighted_product_generator
import Theorems.Thm_OAI_PhysicalGenerator_dissipator_entry
import Theorems.Thm_OAI_PhysicalGenerator_pairing_hasSum
import Theorems.Thm_OAI_WeightedGenerator_pairing_hasSum

-- ---- from OAI.InformationTheory.PhotonNumber.BeamForms ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end CrossEnsemble

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped ComplexConjugate
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

end

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

end BeamLadder

namespace EnsemblePullback

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I : Type*}

end

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable {I J : Type*}

end EnsemblePullback

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end BeamLadder

namespace CrossEnsemble
variable {E J : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {I : Type*}
theorem pairing_selfAdjoint_sandwich (x y : I → E) (P Z : E →L[ℂ] E)
    (hP : IsSelfAdjoint P) :
    pairing x y (P ∘L Z ∘L P)=pairing (fun i => P (x i)) (fun i => P (y i)) Z := by
  unfold pairing
  apply tsum_congr
  intro i
  simp only [ContinuousLinearMap.comp_apply]
  exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hP (y i) (Z (P (x i)))).symm
end CrossEnsemble

namespace Annihilation
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ}

end Annihilation

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I : Type*}

theorem gain_inverse_apply (j : Fin n) (u : Bool) (x : Fock n) :
    inverseWeight 2 (gain j u x)=
      if u then creationSandwich 0 3 (by omega) j x else sandwich 0 3 (by omega) j x := by
  cases u
  · exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (sandwich_factor 2 3 (by omega) j).symm
  · exact congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (creationSandwich_factor 2 3 (by omega) j).symm

theorem inverse_two_one (x : Fock n) : inverseWeight 2 (inverseWeight 1 x)=inverseWeight 3 x :=
  congrArg (fun T : Fock n →L[ℂ] Fock n => T x) (inverseWeight_add 2 1).symm

theorem weighted_pairing_physical (r : ℝ) (x : I → Fock n)
    (Z : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r x (inverseWeight 2 ∘L Z ∘L inverseWeight 2)=
      singleGeneratorPairing r x Z := by
  simp only [WeightedGenerator.pairing,singleGeneratorPairing,
    CrossEnsemble.pairing_selfAdjoint_sandwich _ _ _ _ (inverseWeight_selfAdjoint 2),
    gain_inverse_apply,inverse_two_one,Bool.false_eq_true,ite_false,ite_true]
end BeamLadder

namespace WeightedGenerator
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I K : Type*}

end WeightedGenerator

namespace BeamLadder

section
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J : Type*}

end

open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ} {I J K : Type*}

end BeamLadder

namespace CrossEnsemble
open EntropyPhotonNumber
open scoped ComplexConjugate
variable {n : ℕ} {I : Type*}

end CrossEnsemble

end

end OAI

-- ---- from OAI.InformationTheory.PhotonNumber.Generator ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

noncomputable section

open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I : Type*}

theorem lowerCoefficient_self (j : Fin n) (k : NumberIndex n) :
    lowerCoefficient j k*conj (lowerCoefficient j k)=(k j:ℂ)+1 := by
  simp only [lowerCoefficient,Complex.conj_ofReal,← Complex.ofReal_mul,
    Real.mul_self_sqrt (by positivity : 0≤(k j:ℝ)+1)]
  push_cast
  rfl

theorem raiseCoefficient_self (j : Fin n) (k : NumberIndex n) :
    raiseCoefficient j k*conj (raiseCoefficient j k)=(k j:ℂ) := by
  by_cases hk : k j=0
  · simp [raiseCoefficient,hk]
  · simp only [raiseCoefficient,ite_eq_right hk,Complex.conj_ofReal,← Complex.ofReal_mul,
      Real.mul_self_sqrt (Nat.cast_nonneg (k j)), Complex.ofReal_natCast]

theorem modeCoefficient_conj (j : Fin n) (u : Bool) (k : NumberIndex n) :
    conj (modeCoefficient j u k)=modeCoefficient j u k := by
  cases u <;> simp [modeCoefficient]

theorem generator_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, ((r+1:ℝ):ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) : generator r x=0 := by
  have hj (j : Fin n) : ((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x=0 := by
    apply entry_ext
    intro k l
    have hs : entry (((r+1:ℝ):ℂ) • dissipator j false x+(r:ℂ) • dissipator j true x) k l=
      ((r+1:ℝ):ℂ)*entry (dissipator j false x) k l+(r:ℂ)*entry (dissipator j true x) k l := by
      simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
    rw [hs,dissipator_entry x hx j false,dissipator_entry x hx j true]
    simp only [Bool.false_eq_true,ite_false,ite_true,he,modeCoefficient_conj]
    by_cases hkl : k=l
    · subst l
      simp only [ite_true,lowerCoefficient_self,raiseCoefficient_self,modeCoefficient,
        Bool.false_eq_true,ite_false,add_zero,ite_true,entry,zero_apply,inner_zero_right]
      have hb1 := hb j k
      by_cases hk : k j=0
      · simp only [hk,Nat.cast_zero,zero_add,one_mul,zero_mul,add_zero,mul_zero,sub_zero]
        linear_combination hb1
      · have hb2 := hb j (down j k)
        rw [up_down j k (Nat.pos_of_ne_zero hk)] at hb2
        linear_combination ((k j:ℂ)+1)*hb1-(k j:ℂ)*hb2
    · have hup : up j k≠up j l := fun h => hkl (up_injective j h)
      have hr : raiseCoefficient j k*conj (raiseCoefficient j l)*
          (if down j k=down j l then (p (down j k):ℂ) else 0)=0 := by
        by_cases hk : k j=0
        · simp [raiseCoefficient,hk]
        by_cases hl : l j=0
        · simp [raiseCoefficient,hl]
        have hd : down j k≠down j l := by
          intro hh
          have hh' := congrArg (up j) hh
          rw [up_down j k (Nat.pos_of_ne_zero hk),up_down j l (Nat.pos_of_ne_zero hl)] at hh'
          exact hkl hh'
        rw [ite_eq_right hd,mul_zero]
      rw [ite_eq_right hkl,ite_eq_right hup,hr]
      simp only [mul_zero,sub_zero,add_zero,entry,zero_apply,inner_zero_right]
  simp only [generator,hj,Finset.sum_const_zero]

theorem weighted_pairing_zero_of_geometric_diagonal (r : ℝ) (p : NumberIndex n → ℝ)
    (hb : ∀ j k, ((r+1:ℝ):ℂ)*(p (up j k):ℂ)=(r:ℂ)*(p k:ℂ))
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (p k:ℂ) else 0) (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r x B=0 := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) :=
    HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  have hg := generator_zero_of_geometric_diagonal r p hb x hx he
  have hzero : HasSum (fun _ : NumberIndex n => (0:ℂ)) 0 := hasSum_zero
  have hphys (Z : Fock n →L[ℂ] Fock n) : singleGeneratorPairing r x Z=0 := by
    have hh := pairing_hasSum bas r x hx Z
    have hz : HasSum (fun _ : NumberIndex n => (0:ℂ)) (singleGeneratorPairing r x Z) := by
      simpa only [hg,zero_apply,map_zero,inner_zero_right] using hh
    exact hz.unique hzero
  apply weighted_trace_ext bas (WeightedGenerator.generator r x) 0
    (WeightedGenerator.pairing r x) (fun _ => 0)
    (fun Z => WeightedGenerator.pairing_hasSum bas r x hx Z)
    (fun Z => by simpa only [zero_apply,map_zero,inner_zero_right] using hzero)
    (fun Z => by rw [weighted_pairing_physical,hphys]) B
end PhysicalGenerator

namespace QuantumTrace
theorem thermalWeight_number (n : ℕ) (r : ℝ) (k : Fin n → ℕ) :
    thermalWeight n r k=(r+1)⁻¹^n*(r/(r+1))^(∑ j,k j) := by
  simp [thermalWeight,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]

theorem thermalWeight_up {n : ℕ} (r : ℝ) (j : Fin n) (k : Fin n → ℕ) :
    thermalWeight n r (Annihilation.up j k)=r/(r+1)*thermalWeight n r k := by
  have hs : (∑ i,Annihilation.up j k i)=(∑ i,k i)+1 := by
    simp [Annihilation.up,Finset.sum_add_distrib]
  rw [thermalWeight_number,thermalWeight_number,hs,pow_succ]
  ring

theorem thermalWeight_balance {n : ℕ} (r : ℝ) (hr : 0<r) (j : Fin n) (k : Fin n → ℕ) :
    ((r+1:ℝ):ℂ)*(thermalWeight n r (Annihilation.up j k):ℂ)=
      (r:ℂ)*(thermalWeight n r k:ℂ) := by
  have h : (r+1)*thermalWeight n r (Annihilation.up j k)=r*thermalWeight n r k := by
    rw [thermalWeight_up]
    have hr1 : r+1≠0 := by positivity
    field_simp
  exact_mod_cast h
end QuantumTrace

namespace PhysicalGenerator

section
open EntropyPhotonNumber QuantumTrace
variable {n : ℕ} {I : Type*}

theorem weighted_thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (x : I → Fock n) (hx : Summable (fun i => ‖x i‖^2))
    (he : ∀ k l, entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l=
      if k=l then (thermalWeight n r k:ℂ) else 0) (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r x B=0 :=
  weighted_pairing_zero_of_geometric_diagonal r (thermalWeight n r)
    (thermalWeight_balance r hr) x hx he B
end

open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

theorem dissipator_affine (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y))
    (j : Fin n) (u : Bool) : dissipator j u z=c • dissipator j u x+d • dissipator j u y := by
  have he' (k l : NumberIndex n) :
      entry (CrossEnsemble.operator (baseFamily z) (baseFamily z)) k l=
      c*entry (CrossEnsemble.operator (baseFamily x) (baseFamily x)) k l+
      d*entry (CrossEnsemble.operator (baseFamily y) (baseFamily y)) k l := by
    rw [he]
    simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  apply entry_ext
  intro k l
  have hs : entry (c • dissipator j u x+d • dissipator j u y) k l=
      c*entry (dissipator j u x) k l+d*entry (dissipator j u y) k l := by
    simp only [entry,add_apply,smul_apply,inner_add_right,inner_smul_right]
  rw [hs,dissipator_entry z hz,dissipator_entry x hx,dissipator_entry y hy]
  simp only [he']
  cases u <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> ring

theorem generator_affine (r : ℝ) (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) :
    generator r z=c • generator r x+d • generator r y := by
  unfold generator
  simp only [dissipator_affine c d x y z hx hy hz he,smul_add,Finset.smul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  module

theorem pairing_affine (r : ℝ) (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) (Z : Fock n →L[ℂ] Fock n) :
    singleGeneratorPairing r z Z=c*singleGeneratorPairing r x Z+d*singleGeneratorPairing r y Z := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply (pairing_hasSum bas r z hz Z).unique
  rw [generator_affine r c d x y z hx hy hz he]
  simpa only [add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
    ((pairing_hasSum bas r x hx Z).mul_left c).add ((pairing_hasSum bas r y hy Z).mul_left d)

theorem weighted_pairing_affine (r : ℝ) (c d : ℂ) (x : I → Fock n) (y : J → Fock n) (z : K → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (hy : Summable (fun j => ‖y j‖^2))
    (hz : Summable (fun k => ‖z k‖^2))
    (he : CrossEnsemble.operator (baseFamily z) (baseFamily z)=
      c • CrossEnsemble.operator (baseFamily x) (baseFamily x)+
      d • CrossEnsemble.operator (baseFamily y) (baseFamily y)) (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing r z B=c*WeightedGenerator.pairing r x B+d*WeightedGenerator.pairing r y B := by
  let bas : HilbertBasis (NumberIndex n) ℂ (Fock n) := HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)
  apply weighted_trace_ext bas (WeightedGenerator.generator r z)
    (c • WeightedGenerator.generator r x+d • WeightedGenerator.generator r y)
    (WeightedGenerator.pairing r z) (fun Z => c*WeightedGenerator.pairing r x Z+d*WeightedGenerator.pairing r y Z)
  · exact fun Z => WeightedGenerator.pairing_hasSum bas r z hz Z
  · intro Z
    simpa only [add_apply,smul_apply,map_add,map_smul,inner_add_right,inner_smul_right] using
      ((WeightedGenerator.pairing_hasSum bas r x hx Z).mul_left c).add
        ((WeightedGenerator.pairing_hasSum bas r y hy Z).mul_left d)
  · intro Z
    simp only [weighted_pairing_physical]
    exact pairing_affine r c d x y z hx hy hz he Z
end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder

namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

theorem base_density :
    CrossEnsemble.operator (PhysicalGenerator.baseFamily X.vector) (PhysicalGenerator.baseFamily X.vector)=ρ.op :=
  X.density

theorem thermal_pairing_zero (r : ℝ) (hr : 0<r)
    (he : ∀ k l, entry ρ.op k l=if k=l then (thermalWeight n r k:ℂ) else 0)
    (B : Fock n →L[ℂ] Fock n) : WeightedGenerator.pairing r X.vector B=0 := by
  apply PhysicalGenerator.weighted_thermal_pairing_zero r hr X.vector X.summable
  intro k l
  rw [X.base_density,he]
end WeightedColumns

theorem weighted_replaced_threeport_generator
    {n : ℕ} (η θ κ a b d : ℝ) (hη : η ∈ Set.Icc 0 1) (hθ : θ ∈ Set.Icc 0 1)
    (ρ σ τD m γ ω ρ0 : State n)
    (h1 : IsBeamSplitterOutput η ρ σ m) (h2 : IsBeamSplitterOutput θ m τD γ)
    (X : WeightedColumns ρ) (Y : WeightedColumns σ) (D : WeightedColumns τD)
    (M : WeightedColumns m) (G : WeightedColumns γ) (O : WeightedColumns ω) (Z : WeightedColumns ρ0)
    (hd : 0<d) (hr0 : 0<θ*(η*a+(1-η)*b)+(1-θ)*d)
    (hD : ∀ k l, entry τD.op k l=if k=l then (thermalWeight n d k:ℂ) else 0)
    (hO : ∀ k l, entry ω.op k l=
      if k=l then (thermalWeight n (θ*(η*a+(1-η)*b)+(1-θ)*d) k:ℂ) else 0)
    (hZ : ρ0.op=((1-κ:ℝ):ℂ) • γ.op+(κ:ℂ) • ω.op)
    (B : Fock n →L[ℂ] Fock n) :
    WeightedGenerator.pairing (θ*(η*a+(1-η)*b)+(1-θ)*d) Z.vector B=
      ((1-κ:ℝ):ℂ)*(WeightedGenerator.pairing a X.vector (Y.slice η hη (D.slice θ hθ B))+
        WeightedGenerator.pairing b Y.vector (X.sliceRight η hη (D.slice θ hθ B))) := by
  have he := PhysicalGenerator.weighted_pairing_affine
    (θ*(η*a+(1-η)*b)+(1-θ)*d) ((1-κ:ℝ):ℂ) (κ:ℂ) G.vector O.vector Z.vector
    G.summable O.summable Z.summable (by rw [Z.base_density,G.base_density,O.base_density,hZ]) B
  rw [he,O.thermal_pairing_zero _ hr0 hO,mul_zero,add_zero]
  have hh2 := weighted_product_generator θ (η*a+(1-η)*b) d hθ m τD γ h2
    M.vector D.vector G.vector M.summable D.summable G.summable
    M.normalized D.normalized M.density D.density G.density B
  have hh1 := weighted_product_generator η a b hη ρ σ m h1
    X.vector Y.vector M.vector X.summable Y.summable M.summable
    X.normalized Y.normalized X.density Y.density M.density (D.slice θ hθ B)
  change WeightedGenerator.pairing _ G.vector B=
    WeightedGenerator.pairing _ M.vector (D.slice θ hθ B)+
      WeightedGenerator.pairing d D.vector (M.sliceRight θ hθ B) at hh2
  rw [D.thermal_pairing_zero d hd hD,add_zero,hh1] at hh2
  rw [hh2]
  rfl
end EntropyPhotonNumber

namespace PhysicalGenerator
open EntropyPhotonNumber QuantumTrace Annihilation BeamLadder
open scoped BigOperators ComplexConjugate
variable {n : ℕ} {I J K : Type*}

end PhysicalGenerator

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace KrausBounded
variable {E H I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
end KrausBounded

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}
end BeamLadder

namespace EntropyPhotonNumber
open QuantumTrace Annihilation BeamLadder TensorLp
namespace WeightedColumns
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

namespace BeamLadder
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

end BeamLadder

namespace EntropyPhotonNumber

namespace WeightedColumns
open QuantumTrace Annihilation BeamLadder
variable {n : ℕ} {ρ : State n} (X : WeightedColumns ρ)

end WeightedColumns

end EntropyPhotonNumber

end

end OAI

-- ---- platform node ----
open OAI OAI.EntropyPhotonNumber
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open QuantumTrace Annihilation BeamLadder


theorem solution : type_of% @_root_.OAI.EntropyPhotonNumber.weighted_replaced_threeport_generator := @_root_.OAI.EntropyPhotonNumber.weighted_replaced_threeport_generator
