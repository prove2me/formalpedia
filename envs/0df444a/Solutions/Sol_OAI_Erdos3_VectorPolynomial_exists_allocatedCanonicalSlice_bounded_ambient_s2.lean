-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:08:05.661983+00:00
-- url     : https://prove2.me/submissions/a7869c3b-68a2-40d4-965d-69ef201b0618

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B236
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocated_supported_affine_accurate_ambient_s2
import Theorems.Thm_OAI_Erdos3_canonicalSlicedModulus_good_s2
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_restrict_weight_pos_s2
import Theorems.Thm_OAI_Erdos3_goodKernelUniformCandidate_spec_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueRefinedPeriod
namespace OAI

section

namespace Erdos3

theorem residueLatticeImage_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    (residueLatticeImage L m).toAddSubgroup.index = L.toAddSubgroup.index := by
  have hk : (integerResidueMap I m).toAddMonoidHom.ker ≤ L.toAddSubgroup := by
    change (LinearMap.ker (integerResidueMap I m)).toAddSubgroup ≤ L.toAddSubgroup
    rw [integerResidueMap_ker]
    exact hperiod
  have h := L.toAddSubgroup.index_map_eq (integerResidueMap_surjective I m) hk
  change (L.toAddSubgroup.map (integerResidueMap I m).toAddMonoidHom).index = _
  exact h

theorem residueLatticeImage_card_mul_index {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = m ^ Fintype.card I := by
  classical
  have h := (residueLatticeImage L m).toAddSubgroup.card_mul_index
  rw [residueLatticeImage_index L m hperiod] at h
  change Nat.card (residueLatticeImage L m) * L.toAddSubgroup.index = Nat.card (I → ZMod m) at h
  have heq : Nat.card (I → ZMod m) = m ^ Fintype.card I := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card]
  exact h.trans heq

end Erdos3

end

section

namespace Erdos3

theorem residueLatticeImage_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (m : ℕ) [NeZero m]
    (hperiod : integerScalarLattice I (m : ℤ) ≤ L) :
    L.toAddSubgroup.index ≤ m ^ Fintype.card I := by
  have h := residueLatticeImage_card_mul_index L m hperiod
  have hpos := Nat.card_pos (α := residueLatticeImage L m)
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedKernelPrimitiveBudget
namespace OAI


namespace Erdos3

theorem hasBoundedScalarPeriod_index_le {I : Type*} [Fintype I]
    (L : Submodule ℤ (I → ℤ)) (B : ℕ) (h : HasBoundedScalarPeriod L B) :
    L.toAddSubgroup.index ≤ B ^ Fintype.card I := by
  obtain ⟨a, ha, haB, hperiod⟩ := h
  let : NeZero a := ⟨ha.ne'⟩
  exact (residueLatticeImage_index_le L a hperiod).trans (Nat.pow_le_pow_left haB _)

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.SmoothAffinePairLaw
namespace OAI


namespace Erdos3

open scoped Matrix

theorem integerMatrix_fromCols_range {I J N : Type*} [Fintype J] [Fintype N]
    (B : Matrix I J ℤ) (C : Matrix I N ℤ) :
    (Matrix.fromCols B C).mulVecLin.range = B.mulVecLin.range ⊔ C.mulVecLin.range := by
  ext v
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨B *ᵥ (fun j => x (.inl j)), ⟨_, rfl⟩,
      C *ᵥ (fun n => x (.inr n)), ⟨_, rfl⟩, ?_⟩
    exact (Matrix.fromCols_mulVec B C x).symm.trans hx
  · rintro ⟨b, ⟨x, rfl⟩, c, ⟨y, rfl⟩, h⟩
    refine ⟨Sum.elim x y, ?_⟩
    change Matrix.fromCols B C *ᵥ Sum.elim x y = v
    rw [Matrix.fromCols_mulVec_sumElim]
    exact h

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelScaleIndependence
namespace OAI


namespace Erdos3

theorem scalarKernelJet_extended_period {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    HasBoundedScalarPeriod (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range (B ^ h) := by
  obtain ⟨a, ha, haB, hp⟩ := hx.2
  refine ⟨a ^ h, pow_pos ha h, Nat.pow_le_pow_left haB h, ?_⟩
  rw [integerMatrix_fromCols_range, Nat.cast_pow]
  exact (boundedDegreeIntegerJetMatrix_period _ _ (a : ℤ) hp h rows hr hrows).trans le_sup_left

theorem scalarKernelJet_extended_index {I J O N : Type*}
    [Fintype I] [DecidableEq I] [Fintype J] [Fintype O] [Fintype N]
    {L B : ℕ} {κ : ℝ} (selection : I → J) (x : J → IntegerScalarCubeBox I L)
    (hx : GoodScalarKernelTuple selection κ B x) (h : ℕ) (rows : O → Finset I)
    (hr : Function.Injective rows) (hrows : ∀ o, (rows o).card ≤ h) (C : Matrix O N ℤ) :
    (Matrix.fromCols (scalarKernelIntegerJet x h rows) C).mulVecLin.range.toAddSubgroup.index ≤
      (B ^ h) ^ Fintype.card O :=
  hasBoundedScalarPeriod_index_le _ _ (scalarKernelJet_extended_period selection x hx h rows hr hrows C)


end Erdos3

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientRowReindex
namespace OAI


namespace Erdos3

theorem coefficientImageMultiplier_nonneg {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) : 0 ≤ coefficientImageMultiplier A v := by
  classical
  unfold coefficientImageMultiplier
  split <;> positivity

theorem coefficientImageMultiplier_le_index {I J : Type*} [Fintype J]
    (A : Matrix I J ℤ) (v : I → ℤ) :
    coefficientImageMultiplier A v ≤ (A.mulVecLin.range.toAddSubgroup.index : ℝ) := by
  classical
  unfold coefficientImageMultiplier
  split <;> simp


open MeasureTheory
open scoped BigOperators NNReal

end Erdos3


end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.KernelCoefficientLogBudget
namespace OAI

section

namespace Erdos3

theorem integerScalarLattice_le_of_nat_dvd {O : Type*} [Fintype O] {a b : ℕ}
    (h : a ∣ b) : integerScalarLattice O (b : ℤ) ≤ integerScalarLattice O (a : ℤ) := by
  obtain ⟨c, rfl⟩ := h
  rintro y ⟨z, rfl⟩
  refine ⟨(c : ℤ) • z, ?_⟩
  change (a : ℤ) • ((c : ℤ) • z) = ((a * c : ℕ) : ℤ) • z
  rw [smul_smul, Nat.cast_mul]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.AllocatedFixedKernelReplacement
namespace OAI

section

namespace Erdos3

theorem layerKernelIndexBound_row {m B : ℕ} {α O : Type*} [Fintype α] [Fintype O]
    (hB : 0 < B) (hq : Fintype.card α ≤ m+1) (rows : O → Finset α)
    (hinj : Function.Injective rows) (j : Fin m) :
    (B^(j.val+1))^Fintype.card O ≤ layerKernelIndexBound m B := by
  have hc : Fintype.card O ≤ 2^(m+1) := by
    have hr : Fintype.card O ≤ 2^Fintype.card α := by
      simpa only [Fintype.card_finset] using Fintype.card_le_of_injective rows hinj
    exact hr.trans (Nat.pow_le_pow_right (by decide : 0 < 2) hq)
  rw [← pow_mul]
  exact Nat.pow_le_pow_right hB (Nat.mul_le_mul (Nat.succ_le_of_lt j.isLt) hc)

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped Matrix

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α] (x : G → IntegerScalarCubeBox α S.value)
variable {O : Fin m → Type*} [∀ j, Fintype (O j)]
variable (rows : ∀ j, O j → Finset α)

theorem allocatedIntegerKernelMask_bound {M : ℕ} {κ : ℝ} (hM : 0 < M)
    (selection : α ↪ G) (hx : GoodScalarKernelTuple selection κ M x)
    (hq : Fintype.card α ≤ m + 1) (hinj : ∀ j, Function.Injective (rows j))
    (hrows : ∀ j o, (rows j o).card ≤ j.val + 1)
    (j : Fin m) (modulus : ℕ)
    (residue : Matrix (O j) (AllocatedNonkernelCoefficient (G := G) B j) (ZMod modulus))
    (z : O j → ℤ) :
    0 ≤ allocatedIntegerKernelMask B U basis S x rows j modulus residue z ∧
      allocatedIntegerKernelMask B U basis S x rows j modulus residue z ≤ layerKernelIndexBound m M := by
  unfold allocatedIntegerKernelMask coefficientResidueMultiplier
  refine ⟨coefficientImageMultiplier_nonneg _ _, (coefficientImageMultiplier_le_index _ _).trans ?_⟩
  have hi := scalarKernelJet_extended_index selection x hx (j.val + 1) (rows j)
    (hinj j) (hrows j) (liftResidueMatrix residue)
  exact_mod_cast hi.trans (layerKernelIndexBound_row hM hq (rows j) (hinj j) j)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedNaturalChartScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped Classical

variable {m : ℕ} {G : Type*}
variable {I : Fin m → Type*} {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R : Fin m → ℝ} (hR : ∀ j, 0 < R j) (j : Fin m) (i : Fin (n j))

local notation "scale" => allocatedPrincipalGridScale (G := G) B U basis (R := R) j i

include hR in
theorem allocatedPrincipalGridScale_pos_of_radius : 0 < scale := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (principalProfileSize_pos (hR j) _)
    (Nat.cast_pos.mpr (basisAxisScale_pos (basis j) i))

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

local notation "axisN" => allocatedGridNaturalScale B U b S

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridNaturalScale_pos (a : gridAxes) : 0 < axisN a :=
  allocatedPrincipalGridScale_pos_of_radius B U b hR (ig a).1 (ig a).2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedDetectedCanonicalPeriod
namespace OAI

section

namespace Erdos3
open scoped Classical BigOperators

variable {α G X : Type*} [Fintype α] [DecidableEq α] [Fintype G] [Fintype X]
variable {L M : ℕ} (selection : α ↪ G) (stride : X → ℕ) (height : ℕ)

theorem canonicalSlicedModulus_candidate_dvd
    (x : G → IntegerScalarCubeBox α L)
    (hx : GoodScalarKernelTuple selection (1 / (M : ℝ)) M x)
    (candidate : Fin M) (hc : candidate = goodKernelUniformCandidate selection x hx height) :
    kernelPeriodCandidate (height + 1) candidate ∣
      canonicalSlicedModulus (M := M) selection stride height x := by
  subst candidate
  rw [canonicalSlicedModulus_good_s2 selection stride height x hx]
  exact ⟨∏ i, stride i, rfl⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedClippedFullGridGlobal
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

include hR in
omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] [Fintype α] [DecidableEq α] in
theorem allocatedFullGridNaturalVolume_pos : 0 < allocatedFullGridNaturalVolume B U b S rowSets :=
  Finset.prod_pos (fun a _ => pow_pos (Nat.cast_pos.mpr (allocatedGridNaturalScale_pos B U b hR S a)) _)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineAmbientPrimitiveBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem affineAmbientMassLog_nonneg {P : ℝ} (hP : 0 ≤ P) :
    0 ≤ affineAmbientMassLog P := by unfold affineAmbientMassLog; positivity

theorem affineAmbientMass_le_exp {P Q inv mask : ℝ} {sites axes labels : ℕ}
    (hP : 0 ≤ P) (hQ : 0 ≤ Q) (hQP : Q ≤ P)
    (hsites : (sites : ℝ) ≤ P) (haxes : (axes : ℝ) ≤ P)
    (hlabels : (labels : ℝ) ≤ Real.exp P)
    (hinv0 : 0 ≤ inv) (hinv : inv ≤ Real.exp P)
    (hmask0 : 0 ≤ mask) (hmask : mask ≤ Real.exp P) :
    (Real.toNNReal ((2 : ℝ) ^ sites * inv * ((labels : ℝ) ^ sites * mask *
      Real.exp ((sites * axes : ℕ) * (4 * Q + 8) + Q))) : ℝ) ≤
        Real.exp (affineAmbientMassLog P) := by
  rw [Real.toNNReal_of_nonneg (by positivity)]
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  have hpow : (2 : ℝ) ^ sites ≤ Real.exp (2 * P) := by
    apply (pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) htwo sites).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hl : (labels : ℝ) ^ sites ≤ Real.exp (P ^ 2) := by
    apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hlabels sites).trans
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hexp : Real.exp ((sites * axes : ℕ) * (4 * Q + 8) + Q) ≤
      Real.exp (P ^ 2 * (4 * P + 8) + P) := by
    apply Real.exp_le_exp.mpr
    push_cast
    have hsa : (sites : ℝ) * axes ≤ P ^ 2 := by
      simpa only [pow_two] using mul_le_mul hsites haxes (Nat.cast_nonneg _) hP
    have hh := mul_le_mul hsa (show 4 * Q + 8 ≤ 4 * P + 8 by linarith)
      (by linarith : 0 ≤ 4 * Q + 8) (sq_nonneg P)
    linarith
  calc
    _ ≤ Real.exp (2 * P) * Real.exp P *
        (Real.exp (P ^ 2) * Real.exp P * Real.exp (P ^ 2 * (4 * P + 8) + P)) :=
      mul_le_mul (mul_le_mul hpow hinv hinv0 (Real.exp_nonneg _))
        (mul_le_mul (mul_le_mul hl hmask hmask0 (Real.exp_nonneg _)) hexp
          (Real.exp_nonneg _) (by positivity)) (by positivity) (by positivity)
    _ = _ := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold affineAmbientMassLog
      ring

theorem affineAmbientLift_le_exp {P : ℝ} (hP : 0 ≤ P)
    {N mass Lgrid d sites Lsite Lrows : ℝ≥0}
    (hN : (N : ℝ) ≤ Real.exp P) (hmass : (mass : ℝ) ≤ Real.exp (affineAmbientMassLog P))
    (hg : (Lgrid : ℝ) ≤ Real.exp P) (hd : (d : ℝ) ≤ Real.exp P)
    (hs : (sites : ℝ) ≤ Real.exp P) (hl : (Lsite : ℝ) ≤ Real.exp P)
    (hr : (Lrows : ℝ) ≤ Real.exp P) :
    ((N * mass : ℝ≥0) : ℝ) ≤ Real.exp (affineAmbientMassLog P + P) ∧
      ((N * (mass * (Lgrid * d) + mass * (sites * (Lsite * Lrows))) : ℝ≥0) : ℝ) ≤
        Real.exp (2 * affineAmbientMassLog P + 7 * P + 1) := by
  have hM := affineAmbientMassLog_nonneg hP
  constructor
  · simp only [NNReal.coe_mul]
    exact (mul_le_mul hN hmass mass.coe_nonneg (Real.exp_nonneg _)).trans_eq (by
      rw [← Real.exp_add, add_comm])
  · simp only [NNReal.coe_mul, NNReal.coe_add]
    rw [mul_add]
    have hfirst : (N : ℝ) * (mass * (Lgrid * d)) ≤ Real.exp (affineAmbientMassLog P + 3 * P) := by
      calc
        _ ≤ Real.exp P * (Real.exp (affineAmbientMassLog P) * (Real.exp P * Real.exp P)) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    have hsecond : (N : ℝ) * (mass * (sites * (Lsite * Lrows))) ≤
        Real.exp (affineAmbientMassLog P + 4 * P) := by
      calc
        _ ≤ Real.exp P * (Real.exp (affineAmbientMassLog P) *
          (Real.exp P * (Real.exp P * Real.exp P))) := by gcongr
        _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
    exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
      (congrArg Real.exp (by ring))

theorem affineAmbientSiteLip_le_exp {P : ℝ} (hP : 0 ≤ P)
    {axes cutoff r coord L : ℝ≥0} {d period : ℕ}
    (ha : (axes : ℝ) ≤ Real.exp P) (hc : (cutoff : ℝ) ≤ Real.exp P)
    (hr : ((2 * r)⁻¹ : ℝ≥0) ≤ Real.exp P) (hcoord : (coord : ℝ) ≤ Real.exp P)
    (hL : (L : ℝ) ≤ Real.exp P) (hd : (d : ℝ) ≤ Real.exp P)
    (hperiod : (period : ℝ) ≤ Real.exp P) :
    (((axes * cutoff / (2 * r)) * coord * d +
      max (L * coord * period) (4 * period) * (d / period : ℕ) : ℝ≥0) : ℝ) ≤
        Real.exp (9 * P + 5) := by
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hfirst : (((axes * cutoff / (2 * r)) * coord * d : ℝ≥0) : ℝ) ≤ Real.exp (5 * P) := by
    simp only [div_eq_mul_inv, NNReal.coe_mul, NNReal.coe_natCast]
    calc
      _ ≤ ((Real.exp P * Real.exp P * Real.exp P) * Real.exp P) * Real.exp P := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hmax : ((max (L * coord * period) (4 * period) : ℝ≥0) : ℝ) ≤ Real.exp (3 * P + 4) := by
    simp only [NNReal.coe_max, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
    apply max_le
    · calc
        _ ≤ Real.exp P * Real.exp P * Real.exp P := by gcongr
        _ = Real.exp (3 * P) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
    · calc
        _ ≤ Real.exp 4 * Real.exp P := by gcongr
        _ = Real.exp (4 + P) := (Real.exp_add _ _).symm
        _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hsecond : ((max (L * coord * period) (4 * period) * (d / period : ℕ) : ℝ≥0) : ℝ) ≤
      Real.exp (4 * P + 4) := by
    simp only [NNReal.coe_mul, NNReal.coe_natCast]
    calc
      _ ≤ Real.exp (3 * P + 4) * Real.exp P := mul_le_mul hmax
        ((Nat.cast_le.mpr (Nat.div_le_self d period)).trans hd) (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  rw [NNReal.coe_add]
  exact (add_le_exp_add_one (by positivity) (by positivity) hfirst hsecond).trans_eq
    (congrArg Real.exp (by ring))

theorem affineAmbientGridLip_le_exp {P : ℝ} (_hP : 0 ≤ P)
    {axes outputs height coord : ℝ≥0}
    (ha : (axes : ℝ) ≤ Real.exp P) (ho : (outputs : ℝ) ≤ Real.exp P)
    (hh : (height : ℝ) ≤ Real.exp P) (hc : (coord : ℝ) ≤ Real.exp P) :
    ((axes * (outputs * (2 * height ^ 2)) * coord : ℝ≥0) : ℝ) ≤ Real.exp (5 * P + 2) := by
  have htwo : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp (2 : ℝ)]
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat]
  calc
    _ ≤ Real.exp P * (Real.exp P * (Real.exp 2 * Real.exp P ^ 2)) * Real.exp P := by gcongr
    _ = _ := by
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 1
      ring

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped NNReal

theorem affineAmbientPrimitive_bounds {base Q inv mask : ℝ}
    {sites axes labels gridaxes outputs d period : ℕ}
    {N K coords cutoff r radius Lrows height : ℝ≥0}
    (hb : 0 ≤ base) (hQ : 0 ≤ Q)
    (hsites : (sites : ℝ) ≤ base) (haxes : (axes : ℝ) ≤ base)
    (hlabels : (labels : ℝ) ≤ Real.exp base)
    (hinv0 : 0 ≤ inv) (hinv : inv ≤ Real.exp base)
    (hmask0 : 0 ≤ mask) (hmask : mask ≤ Real.exp base)
    (hN : (N : ℝ) ≤ Real.exp base) (hK : (K : ℝ) ≤ Real.exp base)
    (hcoords : (coords : ℝ) ≤ Real.exp base) (hc : (cutoff : ℝ) ≤ Real.exp base)
    (hr : 1 ≤ r) (hradius : 1 ≤ radius)
    (hd : (d : ℝ) ≤ Real.exp base) (hperiod : (period : ℝ) ≤ Real.exp base)
    (hrows : (Lrows : ℝ) ≤ Real.exp base)
    (hgaxes : (gridaxes : ℝ) ≤ base) (houtputs : (outputs : ℝ) ≤ base)
    (hheight : (height : ℝ) ≤ Real.exp base) :
    let mass := Real.toNNReal ((2 : ℝ) ^ sites * inv * ((labels : ℝ) ^ sites * mask *
      Real.exp ((sites * axes : ℕ) * (4 * Q + 8) + Q)))
    let L : ℝ≥0 := ⟨Real.exp (axes + 6 * Q + 12), Real.exp_nonneg _⟩ + axes * cutoff / (2 * radius)
    let coord := K * coords
    let Lsite := (axes * cutoff / (2 * r)) * coord * d +
      max (L * coord * period) (4 * period) * (d / period : ℕ)
    let Lgrid := (gridaxes * (outputs * (2 * height ^ 2))) * coords
    let T := affineAmbientPrimitiveBudget base Q
    ((N * mass : ℝ≥0) : ℝ) ≤ Real.exp T ∧
      ((N * (mass * (Lgrid * d) + mass * (sites * (Lsite * Lrows))) : ℝ≥0) : ℝ) ≤ Real.exp T := by
  intro mass L coord Lsite Lgrid T
  let P := base + Q
  let P₁ := 9 * P + 13
  let P₂ := 9 * P₁ + 5
  have hP : 0 ≤ P := add_nonneg hb hQ
  have hbP : base ≤ P := le_add_of_nonneg_right hQ
  have hQP : Q ≤ P := le_add_of_nonneg_left hb
  have hP₁ : 0 ≤ P₁ := by dsimp [P₁]; positivity
  have hP₂ : 0 ≤ P₂ := by dsimp [P₂]; positivity
  have hPP₁ : P ≤ P₁ := by dsimp [P₁]; linarith
  have hP₁P₂ : P₁ ≤ P₂ := by dsimp [P₂]; linarith
  have hbP₂ := hbP.trans (hPP₁.trans hP₁P₂)
  have hexp : Real.exp base ≤ Real.exp P₂ := Real.exp_le_exp.mpr hbP₂
  have hbaseE : base ≤ Real.exp base := by linarith [Real.add_one_le_exp base]
  have hL : (L : ℝ) ≤ Real.exp P₁ := by
    have hden : (1 : ℝ) ≤ 2 * (radius : ℝ) := by exact_mod_cast (by linarith : (1 : ℝ≥0) ≤ 2 * radius)
    have hcut : ((axes * cutoff / (2 * radius) : ℝ≥0) : ℝ) ≤ Real.exp (2 * P) := by
      simp only [NNReal.coe_div, NNReal.coe_mul, NNReal.coe_natCast, NNReal.coe_ofNat]
      apply (div_le_self (by positivity) hden).trans
      calc
        _ ≤ Real.exp P * Real.exp P := mul_le_mul
          ((haxes.trans hbaseE).trans (Real.exp_le_exp.mpr hbP))
          (hc.trans (Real.exp_le_exp.mpr hbP)) cutoff.coe_nonneg (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hraw : Real.exp (axes + 6 * Q + 12) ≤ Real.exp (7 * P + 12) :=
      Real.exp_le_exp.mpr (by linarith)
    change Real.exp (axes + 6 * Q + 12) + _ ≤ _
    exact (add_le_exp_add_one (by positivity) (by positivity) hraw hcut).trans_eq
      (congrArg Real.exp (by dsimp [P₁]; ring))
  have hcoord : (coord : ℝ) ≤ Real.exp P₁ := by
    change (K : ℝ) * coords ≤ _
    calc
      _ ≤ Real.exp base * Real.exp base := mul_le_mul hK hcoords coords.coe_nonneg (Real.exp_nonneg _)
      _ = Real.exp (2 * base) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := Real.exp_le_exp.mpr (by dsimp [P₁, P]; linarith)
  have hrInv : (((2 * r)⁻¹ : ℝ≥0) : ℝ) ≤ Real.exp P₁ := by
    have hden : (1 : ℝ≥0) ≤ 2 * r := by linarith
    have hh : (2 * r)⁻¹ ≤ (1 : ℝ≥0) := inv_le_one_of_one_le₀ hden
    exact (NNReal.coe_le_coe.mpr hh).trans (Real.one_le_exp hP₁)
  have hbase₁ : Real.exp base ≤ Real.exp P₁ := Real.exp_le_exp.mpr (hbP.trans hPP₁)
  have hsite : (Lsite : ℝ) ≤ Real.exp P₂ :=
    affineAmbientSiteLip_le_exp hP₁ ((haxes.trans hbaseE).trans hbase₁)
      (hc.trans hbase₁) hrInv hcoord hL (hd.trans hbase₁) (hperiod.trans hbase₁)
  have hgrid : (Lgrid : ℝ) ≤ Real.exp P₂ := by
    apply (affineAmbientGridLip_le_exp (axes := (gridaxes : ℝ≥0)) (outputs := (outputs : ℝ≥0)) hb (hgaxes.trans hbaseE) (houtputs.trans hbaseE) hheight hcoords).trans
    exact Real.exp_le_exp.mpr (by dsimp [P₂, P₁, P]; linarith)
  have hm : (mass : ℝ) ≤ Real.exp (affineAmbientMassLog P₂) :=
    affineAmbientMass_le_exp hP₂ hQ (hQP.trans (hPP₁.trans hP₁P₂))
      (hsites.trans hbP₂) (haxes.trans hbP₂) (hlabels.trans hexp)
      hinv0 (hinv.trans hexp) hmask0 (hmask.trans hexp)
  have hbound := affineAmbientLift_le_exp (d := (d : ℝ≥0)) (sites := (sites : ℝ≥0)) hP₂ (hN.trans hexp) hm hgrid (hd.trans hexp)
    ((hsites.trans hbaseE).trans hexp) hsite (hrows.trans hexp)
  refine ⟨hbound.1.trans (Real.exp_le_exp.mpr ?_), hbound.2⟩
  change affineAmbientMassLog P₂ + P₂ ≤ 2 * affineAmbientMassLog P₂ + 7 * P₂ + 1
  linarith [affineAmbientMassLog_nonneg hP₂]

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedSupportedAffineBoundedAmbient
namespace OAI

section

namespace Erdos3.VectorPolynomial
universe uα

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset α))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox α S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) α (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hperiod : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (period : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable {M : ℝ} (hM : 1 ≤ M)
variable (hm : ∀ j z, 0 ≤ allocatedIntegerKernelMask B U b S x
  (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
  (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
    (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
    (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ∧
  allocatedIntegerKernelMask B U b S x
    (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j q
    (integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
      (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀)
      (fun j => (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)) j
      (principalAxisRestrict (fun a => ¬allocatedGridAxis (I := I) U b S.value a) y₀)) q) z ≤ M)

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset α) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := α) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
variable (hu₀ : (containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell
  (allocatedGridAxis (I := I) U b S.value)).weight (principalAxisRestrict (allocatedGridAxis (I := I) U b S.value) y₀) ≠ 0)
variable (hmodulus : ∀ j, integerScalarLattice {t : Finset α // t ∈ rowSets j} (q : ℤ) ≤
  (scalarKernelIntegerJet x (j.val + 1) (Subtype.val : {t : Finset α // t ∈ rowSets j} → Finset α)).mulVecLin.range)
variable (hy₀ : ∀ j, IntegerScalarCube (allocatedPrincipalSides B U b S j) (fun a => (y₀ j a : ℤ)))
local notation "gridAxes" => {a // grid a}
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

omit [DecidableEq α] in
theorem allocatedRowSlicedSiteRadius_ge_one : 1 ≤ allocatedRowSlicedSiteRadius rowSets := by
  apply NNReal.coe_le_coe.mp
  change (1 : ℝ) ≤ 1 + ∑ j : Fin m, (rowSets j).card * (partitionedIdealRadius α m + 1)
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (Nat.cast_nonneg _) (add_nonneg (partitionedIdealRadius_nonneg α m) zero_le_one)))

include hr hperiod hM hm hR hC hchart hbudget hu₀ hmodulus in
theorem exists_allocated_supported_affine_bounded_ambient
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius α m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card α * ((Fintype.card α : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog)
    {base : ℝ} (hbase : 0 ≤ base)
    (hvbase : Vlog ≤ base) (hnbase : Nlog ≤ base) (hmbase : Mlog ≤ base)
    (hsites : (Fintype.card (Finset α) : ℝ) ≤ base)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ base)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ≤ Real.exp base)
    (hKbase : (K : ℝ) ≤ Real.exp base)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp base)
    (hrone : 1 ≤ r) (hdbase : (d : ℝ) ≤ Real.exp base) (hpbase : (period : ℝ) ≤ Real.exp base)
    (hrows : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ base)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp base) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card α) p
    let budget := affineAmbientPrimitiveBudget base Q
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith ⟨Real.exp budget, Real.exp_nonneg _⟩ F ∧
      (∀ z, ‖F z‖ ≤ Real.exp budget) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤ Real.exp (-target) := by
  intro p Q budget
  obtain ⟨F, hF, hFb, hFe⟩ := exists_allocated_supported_affine_accurate_ambient_s2
    B U b S rowSets x y₀ q d period r hr hb o bW hperiod hM hm hR C hC hchart hbudget
    ρ center width hσ H step c hH hsubset label hcell hu₀ hmodulus hdiv
    Cforward hforward K hK T hT hTideal hsource hradius hσ1 hρ hρ1 hw
    hPbox hPrho hVlog hNlog hMlog htarget hbox hρp hvolume hnormalizer hmask
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hQ : 0 ≤ Q := (idealSiteLogBudget_bounds _ _ hp).1
  have hN : (‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊ : ℝ) ≤ Real.exp base := by
    rw [coe_nnnorm, Complex.norm_real, Real.norm_of_nonneg (allocatedFullGridNaturalVolume_pos B U b hR S rowSets).le]
    exact hvolume.trans (Real.exp_le_exp.mpr hvbase)
  have hradone : 1 ≤ allocatedRowSlicedSiteRadius rowSets :=
    allocatedRowSlicedSiteRadius_ge_one rowSets
  have hmask0 : 0 ≤ M ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period :=
    mul_nonneg (pow_nonneg (zero_le_one.trans hM) _) (coefficientDeckPeriodCap_nonneg rowTypes E period)
  have hprim := affineAmbientPrimitive_bounds (d := d) (period := period)
    (gridaxes := Fintype.card gridAxes)
    (N := ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ)‖₊)
    (K := K) (coords := ∑ j, Cforward j * Fintype.card (J j))
    (cutoff := normalizedSiteCutoffBound) (r := r) (radius := allocatedRowSlicedSiteRadius rowSets)
    (Lrows := ∑ j : Fin m, ((rowSets j).card : ℝ≥0))
    (height := (S.value : ℝ≥0) ^ (layerTailDegree m + 1))
    hbase hQ hsites haxes hlabels (norm_nonneg _) (hnormalizer.trans (Real.exp_le_exp.mpr hnbase))
    hmask0 (hmask.trans (Real.exp_le_exp.mpr hmbase)) hN hKbase hcoords hcutoff hrone hradone
    hdbase hpbase hrows ((Nat.cast_le.mpr (Fintype.card_subtype_le (allocatedGridAxis (I := I) U b S.value))).trans haxes)
    houtputs hheight
  refine ⟨F, hF.weaken ?_, fun z => (hFb z).trans hprim.1, hFe⟩
  exact NNReal.coe_le_coe.mp hprim.2

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.AllocatedCanonicalSliceConstructedModelSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule _root_.Set _root_.OAI.Set
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {dim : ℕ}
variable (rowSets : Fin m → Finset (Finset (Fin dim)))

local notation "rowTypes" => (fun j : Fin m => {t : Finset (Fin dim) // t ∈ rowSets j})
local notation "rows" => (fun j => (Subtype.val : rowTypes j → Finset (Fin dim)))
local notation "grid" => allocatedGridAxis (I := I) U b S.value

variable {E : Fin m → Type*} [∀ j, Fintype (E j)]
variable (x : G → IntegerScalarCubeBox (Fin dim) S.value)
variable (y₀ : PrincipalIntegerTuples B (layerSamplerDegree I n) (Fin dim) (allocatedPrincipalSides B U b S))
variable (q d period : ℕ) [NeZero d] [NeZero period]
variable (r : ℝ≥0) (hr : 0 < r)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable (bW : ∀ j, Basis (E j) ℤ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))

local notation "residue" => (fun j => integerResidueMatrix (allocatedNonkernelJetMatrix B U b S x
  (principalAxisRestrict grid y₀) rows j (principalAxisRestrict (fun a => ¬grid a) y₀)) q)
local notation "inverseNormalizer" => ((allocatedProductIdealNormalizer B U b S rowSets : ℝ) : ℂ)⁻¹

variable (hR : ∀ j, 0 < R j) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hbudget : ∀ j, ((rowSets j).card + 1 : ℝ) * (Fintype.card (Finset (Fin dim)) *
  (C j * (((Fintype.card (I j) : ℝ) + 1) * (2 * (r : ℝ) * R j)))) ≤ 1 / 4)

variable (ρ : ℝ≥0)
variable (center width : PrincipalAxisParameter (B := B) (h := layerSamplerDegree I n)
  (α := Fin dim) (fun a => ¬allocatedGridAxis (I := I) U b S.value a) → ℝ)

variable (hσ : ∀ j, 0 < σ j)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (label : PrincipalTupleIndex B (layerSamplerDegree I n) → Option (Fin dim) → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := Fin dim) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = label)))
local notation "gridLaw" => containedSupportedProgressionAxisLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell grid
local notation "ideal" => allocatedRowSlicedIdeal B U b S rowSets ρ center width

variable {Mk : ℕ} (hMk : 0 < Mk) (selection : Fin dim ↪ G)
variable (hx : GoodScalarKernelTuple selection (1 / (Mk : ℝ)) Mk x)
variable {X : Type*} [Fintype X] (stride : X → ℕ)
variable (hqcanonical : q = canonicalSlicedModulus (M := Mk) selection stride m x)
variable (hperiodcanonical : period = kernelPeriodCandidate (m + 1) (goodKernelUniformCandidate selection x hx m))
variable (hy₀ : 0 < (containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S) hH hsubset q label hcell).weight y₀)

include hr hR hC hchart hbudget hMk hx hqcanonical hperiodcanonical hy₀ in
theorem exists_allocatedCanonicalSlice_bounded_ambient_s2_oai
    (hdim : dim ≤ m + 1)
    (hrowDegree : ∀ j (t : rowSets j), t.val.card ≤ j.val + 1)
    (hdiv : period ∣ d)
    (Cforward : Fin m → ℝ≥0)
    (hforward : ∀ j v, ‖normalizedOrthogonalChart (euclideanSubspace (U j)) (b j) v‖ ≤ Cforward j * ‖v‖)
    (K : ℝ≥0) (hK : ∀ j, (R j)⁻¹ ≤ K)
    (T : Fin m → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hTideal : ∀ j, partitionedIdealRadius (Fin dim) m + 1 ≤ T j)
    (hsource : ∀ j, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) *
      ((2 : ℝ) ^ Fintype.card (Fin dim) * ((Fintype.card (Fin dim) : ℝ) + 1) ^ (j.val + 1)) ≤ T j)
    (hradius : ∀ j, (rowSets j).card * T j ≤ (r : ℝ)) (hσ1 : ∀ j, σ j ≤ 1)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hw : ∀ i, |center i| + |width i| ≤ 1)
    {Pbox Prho Vlog Nlog Mlog target : ℝ}
    (hPbox : 0 ≤ Pbox) (hPrho : 0 ≤ Prho) (hVlog : 0 ≤ Vlog)
    (hNlog : 0 ≤ Nlog) (hMlog : 0 ≤ Mlog) (htarget : 0 ≤ target)
    (hbox : 2 * (allocatedRowSlicedSiteRadius rowSets : ℝ) ≤ Real.exp Pbox)
    (hρp : (ρ : ℝ)⁻¹ ≤ Real.exp Prho)
    (hvolume : allocatedFullGridNaturalVolume B U b S rowSets ≤ Real.exp Vlog)
    (hnormalizer : ‖inverseNormalizer‖ ≤ Real.exp Nlog)
    (hmask : (layerKernelIndexBound m Mk : ℝ) ^ Fintype.card (LayerSamplerAxis I n) * coefficientDeckPeriodCap rowTypes E period ≤ Real.exp Mlog)
    {base : ℝ} (hbase : 0 ≤ base)
    (hvbase : Vlog ≤ base) (hnbase : Nlog ≤ base) (hmbase : Mlog ≤ base)
    (hsites : (Fintype.card (Finset (Fin dim)) : ℝ) ≤ base)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ base)
    (hlabels : (Fintype.card ((∀ j, Fin (n j) → ZMod period) × (∀ j, E j → ZMod period)) : ℝ) ≤ Real.exp base)
    (hKbase : (K : ℝ) ≤ Real.exp base)
    (hcoords : ((∑ j, Cforward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (hcutoff : (normalizedSiteCutoffBound : ℝ) ≤ Real.exp base)
    (hrone : 1 ≤ r) (hdbase : (d : ℝ) ≤ Real.exp base) (hpbase : (period : ℝ) ≤ Real.exp base)
    (hrows : ((∑ j : Fin m, ((rowSets j).card : ℝ≥0) : ℝ≥0) : ℝ) ≤ Real.exp base)
    (houtputs : (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1) : ℝ) ≤ base)
    (hheight : (S.value : ℝ) ^ (layerTailDegree m + 1) ≤ Real.exp base) :
    let p := Pbox + Prho + Vlog + Nlog + Mlog + target
    let Q := idealSiteLogBudget (Fintype.card (Σ a : LayerSamplerAxis I n, rowTypes a.1)) (Fintype.card (Fin dim)) p
    let budget := affineAmbientPrimitiveBudget base Q
    ∃ F : (JetAmbientIndex rowTypes J → UnitAddCircle) → ℂ,
      LipschitzWith ⟨Real.exp budget, Real.exp_nonneg _⟩ F ∧
      (∀ z, ‖F z‖ ≤ Real.exp budget) ∧
      ∀ y : EuclideanJetLayers U rowTypes,
        ‖((gridLaw).mean (fun u => allocatedWholeMaskedCoveredProfile B U b hR hσ S x rows hb o bW d
          (principalAxisJoin grid u (principalAxisRestrict (fun a => ¬grid a) y₀)) q ideal y) : ℂ) -
          F (coveredJetAmbientTorus U 1 y)‖ ≤ Real.exp (-target) := by
  intro p Q budget
  obtain ⟨_, hperiodAll⟩ := goodKernelUniformCandidate_spec_s2 selection x hx m
  have hperiod (j : Fin m) : integerScalarLattice (rowTypes j) (period : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range := by
    rw [hperiodcanonical]
    exact @hperiodAll
      (rowTypes j) (Subtype.fintype _) (j.val + 1) (by omega) (rows j) Subtype.val_injective (hrowDegree j)
  have hqdiv : period ∣ q := by
    rw [hperiodcanonical, hqcanonical]
    exact canonicalSlicedModulus_candidate_dvd selection stride m x hx _ rfl
  have hqimage (j : Fin m) : integerScalarLattice (rowTypes j) (q : ℤ) ≤
      (scalarKernelIntegerJet x (j.val + 1) (rows j)).mulVecLin.range :=
    (integerScalarLattice_le_of_nat_dvd (O := rowTypes j) hqdiv).trans (hperiod j)
  have hM : (1 : ℝ) ≤ (layerKernelIndexBound m Mk : ℝ) := by
    exact_mod_cast (Nat.one_le_pow _ _ (by omega : 1 ≤ Mk))
  have hm := fun j z => allocatedIntegerKernelMask_bound B U b S x rows hMk selection hx
    (by simpa only [Fintype.card_fin] using hdim) (fun _ => Subtype.val_injective)
    hrowDegree j q (residue j) z
  have hu₀ := containedSupportedProgressionLaw_restrict_weight_pos_s2 B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U b S) H step c (allocatedPrincipalSides_pos B U b S)
    hH hsubset q label hcell y₀ hy₀ grid
  exact exists_allocated_supported_affine_bounded_ambient
    B U b S rowSets x y₀ q d period r hr hb o bW hperiod hM hm hR C hC hchart hbudget
    ρ center width hσ H step c hH hsubset label hcell hu₀.ne' hqimage hdiv
    Cforward hforward K hK T hT hTideal hsource hradius hσ1 hρ hρ1 hw
    hPbox hPrho hVlog hNlog hMlog htarget hbox hρp hvolume hnormalizer hmask
    hbase hvbase hnbase hmbase hsites haxes hlabels hKbase hcoords hcutoff hrone hdbase
    hpbase hrows houtputs hheight

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4, u_5, u_6} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6} := @OAI.Erdos3.VectorPolynomial.exists_allocatedCanonicalSlice_bounded_ambient_s2_oai.{u_1, u_2, u_3, u_4, u_5, u_6}
