-- Prove2me | solution 1 for OAI.PettyProjection.brunnMinkowski_classical
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:09:01.184183+00:00
-- url     : https://prove2.me/submissions/13e0b075-ce98-4f29-9241-7455f51a8ffc

import Mathlib
import Definitions.Def_PettyProjectionVolume
import Definitions.Def_OAIQWPP000
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
section
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasureSpace E] [BorelSpace E]
    [Measure.IsAddHaarMeasure (volume : Measure E)]

lemma volumeReal_smul_nonneg {r : ℝ} (hr : 0 ≤ r) (K : Set E) :
    volume.real (r • K)=r^(Module.finrank ℝ E)*volume.real K := by
  rw [Measure.real,Measure.addHaar_smul_of_nonneg volume hr,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (pow_nonneg hr _)]
  rfl

end
end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Pointwise
namespace PettyProjection
section
variable {E : Type uE} {F : Type uF} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F]

omit [MeasureSpace E] [BorelSpace E] [MeasureSpace F] [BorelSpace F] in
lemma linearEquiv_preimage_combo (e : E ≃L[ℝ] F) (K M : Set F) (a b : ℝ) :
    e ⁻¹' (a • K+b • M)=a • (e ⁻¹' K)+b • (e ⁻¹' M) := by
  ext z
  constructor
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,he⟩
    refine ⟨a • e.symm x,⟨e.symm x,by simpa using hx,rfl⟩,
      b • e.symm y,⟨e.symm y,by simpa using hy,rfl⟩,?_⟩
    apply e.injective
    simpa using he
  · rintro ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,rfl⟩
    exact ⟨a • e x,⟨e x,hx,rfl⟩,b • e y,⟨e y,hy,rfl⟩,by simp⟩

omit [BorelSpace E] in
lemma BrunnMinkowskiRoot.equiv {m : ℕ} (hm : BrunnMinkowskiRoot E m)
    (e : E ≃L[ℝ] F) (he : MeasurePreserving e) : BrunnMinkowskiRoot F m := by
  intro K M hK hcK hiK hM hcM hiM a b ha hb hab
  have hPK : IsCompact (e ⁻¹' K) := e.toHomeomorph.isCompact_preimage.mpr hK
  have hPM : IsCompact (e ⁻¹' M) := e.toHomeomorph.isCompact_preimage.mpr hM
  have hiPK : (interior (e ⁻¹' K)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' K)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiK
    exact ⟨e.symm x,by simpa using hx⟩
  have hiPM : (interior (e ⁻¹' M)).Nonempty := by
    change (interior (e.toHomeomorph ⁻¹' M)).Nonempty
    rw [← e.toHomeomorph.preimage_interior]
    obtain ⟨x,hx⟩ := hiM
    exact ⟨e.symm x,by simpa using hx⟩
  have h := hm (e ⁻¹' K) (e ⁻¹' M) hPK (hcK.linear_preimage e.toLinearMap) hiPK
    hPM (hcM.linear_preimage e.toLinearMap) hiPM a b ha hb hab
  have hm' (S : Set F) (hS : IsCompact S) : volume.real (e ⁻¹' S)=volume.real S :=
    congrArg ENNReal.toReal (he.measure_preimage hS.measurableSet.nullMeasurableSet)
  rw [hm' K hK,hm' M hM,← linearEquiv_preimage_combo,hm' _ ((hK.smul _).add (hM.smul _))] at h
  exact h
end

/-- Standard Euclidean volume version used for the projection-body theorem. -/
theorem brunnMinkowski_space {n : ℕ} (hn : 0 < n) : BrunnMinkowskiRoot (Space n) n :=
  brunnMinkowski_euclidean hn

end PettyProjection
end

noncomputable section
open Set MeasureTheory Filter Topology
namespace PettyProjection

/-- Brunn--Minkowski for the canonical Euclidean volume on any finite-dimensional
real inner-product space. -/
theorem brunnMinkowski_innerProduct {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 0 < Module.finrank ℝ E) : BrunnMinkowskiRoot E (Module.finrank ℝ E) := by
  exact (brunnMinkowski_space hE).equiv
    (stdOrthonormalBasis ℝ E).repr.symm.toContinuousLinearEquiv
    (stdOrthonormalBasis ℝ E).measurePreserving_repr_symm

end PettyProjection
end

noncomputable section
open Set MeasureTheory
open scoped Pointwise
namespace PettyProjection

/-- The Brunn–Minkowski inequality, classical additive form: in a finite-dimensional real inner
product space `E` of dimension `n ≥ 1` with its canonical volume, compact convex sets `A`, `B`
with nonempty interior satisfy `vol(A)^(1/n) + vol(B)^(1/n) ≤ vol(A + B)^(1/n)`. -/
theorem brunnMinkowski_classical_oai {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (hE : 0 < Module.finrank ℝ E) {A B : Set E}
    (hA : IsCompact A) (hcA : Convex ℝ A) (hiA : (interior A).Nonempty)
    (hB : IsCompact B) (hcB : Convex ℝ B) (hiB : (interior B).Nonempty) :
    volume.real A ^ ((Module.finrank ℝ E : ℝ)⁻¹) + volume.real B ^ ((Module.finrank ℝ E : ℝ)⁻¹)
      ≤ volume.real (A + B) ^ ((Module.finrank ℝ E : ℝ)⁻¹) := by
  have h := brunnMinkowski_innerProduct hE A B hA hcA hiA hB hcB hiB
    (1/2) (1/2) (by norm_num) (by norm_num) (by norm_num)
  rw [← smul_add, volumeReal_smul_nonneg (by norm_num : (0:ℝ) ≤ 1/2),
    Real.mul_rpow (by positivity) measureReal_nonneg, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 1/2),
    mul_inv_cancel₀ (by exact_mod_cast hE.ne' : (Module.finrank ℝ E : ℝ) ≠ 0),
    Real.rpow_one] at h
  linarith

end PettyProjection
end

end OAI
end

theorem solution.{uE} : type_of% @OAI.PettyProjection.brunnMinkowski_classical_oai.{uE} := @OAI.PettyProjection.brunnMinkowski_classical_oai.{uE}
