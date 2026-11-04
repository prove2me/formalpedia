-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.FreeFock.haarSpatial_mem_vonNeumann
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:11:37.604629+00:00
-- url     : https://prove2.me/submissions/652aff8a-5b2d-4ce8-be83-fbcb457eedd7

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45 u_46 u_47 u_48
universe u_49

open Filter Topology

namespace FreeFock
open Filter Topology
open scoped ENNReal
variable {α : Type u_6} [DecidableEq α]

end FreeFock
open MeasureTheory Set CompactlySupported
open scoped ENNReal
namespace CyclicSpectral
variable {H : Type u_7} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)
end CyclicSpectral

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal

namespace CyclicSpectral

section
open MeasureTheory
variable {H : Type u_19} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
section
open MeasureTheory Filter
variable {H : Type u_20} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end
open MeasureTheory Filter
variable {H : Type u_21} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (A : H →L[ℂ] H) (hA : IsSelfAdjoint A) (ξ : H)

end CyclicSpectral
namespace FreeFock

section
open MeasureTheory
variable {α : Type u_22} [DecidableEq α]

end
open MeasureTheory
variable {α : Type u_23} [DecidableEq α]

end FreeFock
open Filter Topology
open scoped ENNReal

namespace FreeFock

section
open Filter Topology Set MeasureTheory
variable {α : Type u_25} [DecidableEq α]

end
section
open Set
variable {α : Type u_26} [DecidableEq α]

end

section
open Filter Topology
open scoped ENNReal
variable {α : Type u_28} [DecidableEq α]

end
section
open scoped ComplexConjugate
variable {α : Type u_29} [DecidableEq α]

end
section
variable {α : Type u_30} [DecidableEq α]

end
variable {α : Type u_31} [DecidableEq α]

end FreeFock
section

variable {A : Type u_32} [NormedRing A] [NormedAlgebra ℂ A]

end
namespace FreeFock

section
variable {α : Type u_33} [DecidableEq α]

end
variable {α : Type u_34} [DecidableEq α]

end FreeFock

section
variable {α : Type u_35}

end
section
variable {α : Type u_36} {G : Type u_37} [Group G]

end
namespace FreeFock
variable {α : Type u_38} [DecidableEq α]

end FreeFock

namespace CyclicUnitary
open scoped ENNReal
variable {G : Type u_42} {E : Type u_43} [Group G] [DecidableEq G]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (ρ : G →* (E →L[ℂ] E)) (hstar : ∀ g,star (ρ g)=ρ g⁻¹) (ξ : E)

theorem spatial_basis (htrace : ∀ g,inner ℂ ξ (ρ g ξ)=if g=1 then 1 else 0)
    (htotal : (orbitSpan ρ ξ).topologicalClosure=⊤) (g : G) :
    spatial ρ hstar ξ htrace htotal (basis g)=ρ g ξ :=
  GramSpatial.spatial_family _ _ _ _ _ g

end CyclicUnitary
namespace FreeFock
variable {α : Type u_44} [DecidableEq α]

 theorem haarSpatial_basis (g : FreeGroup α) :
    haarSpatial (CyclicUnitary.basis g)=haarOperatorRepresentation g vacuum :=
  CyclicUnitary.spatial_basis _ _ _ _ _ g

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

theorem equiv_mem_centralizer (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (T : A) :
    e T∈StarSubalgebra.centralizer ℂ (e '' S) ↔ T∈StarSubalgebra.centralizer ℂ S := by
  simp only [StarSubalgebra.mem_centralizer_iff]
  constructor
  · intro h U hU
    have h := h (e U) ⟨U,hU,rfl⟩
    constructor
    · apply (EquivLike.injective e); simpa only [map_mul] using h.1
    · apply (EquivLike.injective e); simpa only [map_mul,map_star] using h.2
  · rintro h _ ⟨U,hU,rfl⟩
    have h := h U hU
    constructor
    · simpa only [map_mul] using congrArg e h.1
    · simpa only [map_mul,map_star] using congrArg e h.2

theorem equiv_image_centralizer (e : A ≃⋆ₐ[ℂ] B) (S : Set A) :
    e '' (StarSubalgebra.centralizer ℂ S : Set A)=
      (StarSubalgebra.centralizer ℂ (e '' S) : Set B) := by
  ext T
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (equiv_mem_centralizer e S U).mpr hU
  · intro hT
    refine ⟨e.symm T,?_,e.apply_symm_apply T⟩
    apply (equiv_mem_centralizer e S _).mp
    rw [e.apply_symm_apply]
    exact hT

theorem equiv_mem_bicommutant (e : A ≃⋆ₐ[ℂ] B) (S : Set A) (T : A) :
    e T∈StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (e '' S) : Set B) ↔
    T∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ S : Set A) := by
  rw [← equiv_image_centralizer]
  exact equiv_mem_centralizer e _ T

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

theorem leftRegular_basis (g h : G) :
    leftRegular g (CyclicUnitary.basis h)=CyclicUnitary.basis (g*h) := by
  ext k
  simp only [leftRegular_apply,CyclicUnitary.basis,lp.single_apply,Pi.single_apply]
  congr 1
  exact propext (inv_mul_eq_iff_eq_mul)

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

theorem haarSpatial_intertwines (g : FreeGroup α) :
    haarSpatial.conjStarAlgEquiv (leftRegular g)=haarOperatorRepresentation g := by
  have h : (haarSpatial (α := α)).toContinuousLinearEquiv.toContinuousLinearMap.comp (leftRegular g)=
      (haarOperatorRepresentation g).comp haarSpatial.toContinuousLinearEquiv.toContinuousLinearMap := by
    apply lp.ext_continuousLinearMap (by norm_num : (2:ℝ≥0∞)≠⊤)
    intro h
    apply ContinuousLinearMap.ext
    intro z
    have hz : lp.single (E := fun _ : FreeGroup α => ℂ) 2 h z=z • CyclicUnitary.basis h := by
      ext k
      simp [CyclicUnitary.basis,lp.single_apply,Pi.single_apply]
    change haarSpatial (leftRegular g (lp.single 2 h z))=
      haarOperatorRepresentation g (haarSpatial (lp.single 2 h z))
    rw [hz,map_smul,map_smul,map_smul,map_smul]
    congr 1
    rw [leftRegular_basis,haarSpatial_basis,haarSpatial_basis]
    exact DFunLike.congr_fun (map_mul haarOperatorRepresentation g h) vacuum
  apply ContinuousLinearMap.ext
  intro ξ
  have h := DFunLike.congr_fun h (haarSpatial.symm ξ)
  simpa only [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,ContinuousLinearMap.comp_apply,LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    ContinuousLinearEquiv.coe_coe,LinearIsometryEquiv.apply_symm_apply] using h

theorem haarRepresentation_commutant :
    StarSubalgebra.centralizer ℂ (Set.range (haarOperatorRepresentation (α := α)))=
      gaussianCommutant α := by
  rw [← haar_gaussian_commutant]
  apply le_antisymm
  · apply StarSubalgebra.centralizer_le ℂ
    rintro _ ⟨i,rfl⟩
    exact ⟨FreeGroup.of i,haarOperatorRepresentation_of i⟩
  · intro C hC
    rw [haar_gaussian_commutant] at hC
    rw [StarSubalgebra.mem_centralizer_iff]
    rintro _ ⟨g,rfl⟩
    have hg : haarOperatorRepresentation g∈gaussianAlgebra α :=
      (haarRepresentation g : gaussianAlgebra α).property
    exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hg C hC).1.symm,
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hg) C hC).1.symm⟩

theorem haarSpatial_mem_vonNeumann (T : GroupOperator (FreeGroup α)) :
    haarSpatial.conjStarAlgEquiv T∈gaussianAlgebra α ↔ T∈groupVonNeumann (FreeGroup α) := by
  have he : haarSpatial.conjStarAlgEquiv '' leftTranslations (FreeGroup α)=
      Set.range (haarOperatorRepresentation (α := α)) := by
    rw [leftTranslations_eq_range,← Set.range_comp]
    congr 1
    funext g
    exact haarSpatial_intertwines g
  have h := equiv_mem_bicommutant haarSpatial.conjStarAlgEquiv (leftTranslations (FreeGroup α)) T
  rw [he,haarRepresentation_commutant] at h
  exact h

end FreeFock

end FreeGroupFactorMain

end

end OAI
end

theorem solution.{u_48} : type_of% @OAI.FreeGroupFactorMain.FreeFock.haarSpatial_mem_vonNeumann.{u_48} := @OAI.FreeGroupFactorMain.FreeFock.haarSpatial_mem_vonNeumann.{u_48}
