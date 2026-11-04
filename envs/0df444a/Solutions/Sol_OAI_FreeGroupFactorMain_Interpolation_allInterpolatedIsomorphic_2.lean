-- Prove2me | solution 2 for OAI.FreeGroupFactorMain.Interpolation.allInterpolatedIsomorphic
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T05:26:45.14661+00:00
-- url     : https://prove2.me/submissions/d4064134-2312-4fc5-80f4-08c6ba457493

import Mathlib
import Definitions.Def_FreeGroupFactorProof33
import Theorems.Thm_OAI_FreeGroupFactorMain_generating_haar_tuple
import Theorems.Thm_OAI_FreeGroupFactorMain_generating_haar_tuple_ge_two
import Theorems.Thm_OAI_FreeGroupFactorMain_InfiniteGeneration_generating_tuple
import Theorems.Thm_OAI_FreeGroupFactorMain_FreeFock_haarSpatial_mem_vonNeumann
import Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_spatial_of_trace_iso
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_scalar_hasCornerScaling_weighted
import Theorems.Thm_OAI_FreeGroupFactorMain_Amplification_preferred_scaling_model

set_option linter.all false

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u uG

open scoped ENNReal

end FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_42 u_43

namespace FreeGroupFactorMain.Amplification

open scoped ENNReal

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end

section
variable {A : Type u_42} {B : Type u_43} [CStarAlgebra A] [CStarAlgebra B]

end

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.Interpolation

open Amplification
open scoped ENNReal

end FreeGroupFactorMain.Interpolation

namespace FreeGroupFactorMain

universe u v

def HasNormalTracialIso (G : Type u) (H : Type v) [Group G] [Group H] : Prop :=
  ∃ Φ : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H,
    (∀ T, canonicalTrace (Φ T) = canonicalTrace T) ∧
    @Continuous _ _ (groupUltraweakTopology G) (groupUltraweakTopology H) Φ

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

universe uG uH

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

open scoped ComplexConjugate

theorem normalTracialIso_of_spatial {G : Type uG} {H : Type uH} [Group G] [Group H]
    (e : GroupHilbert G ≃ₗᵢ[ℂ] GroupHilbert H)
    (hδ : e deltaOne = deltaOne)
    (hVN : ∀ T : GroupOperator G,
      T ∈ groupVonNeumann G ↔ e.conjStarAlgEquiv T ∈ groupVonNeumann H) :
    HasNormalTracialIso G H := by
  classical
  refine ⟨spatialGroupIso e hVN, fun T => ?_, spatialGroupIso_normal e hVN⟩
  rw [canonicalTrace_eq_inner, canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne))) =
    inner ℂ deltaOne ((T : GroupOperator G) deltaOne)
  rw [← hδ, e.symm_apply_apply, e.inner_map_map]

open scoped ComplexConjugate ENNReal

open scoped ComplexConjugate

 theorem normalTracialIso_of_haar_total {G : Type uG} {H : Type uH} [Group G] [Group H] [DecidableEq G]
    (ρ : G →* groupVonNeumann H)
    (hstar : ∀ g, star (ρ g) = ρ g⁻¹)
    (htrace : ∀ g, canonicalTrace (ρ g) = if g = 1 then 1 else 0)
    (htotal : ⊤ ≤ (Submodule.span ℂ (Set.range
      (fun g => ((ρ g : groupVonNeumann H) : GroupOperator H) deltaOne))).topologicalClosure) :
    HasNormalTracialIso G H := by
  obtain ⟨e,hδ,_hρ,hVN⟩ := spatial_of_haar_total ρ hstar htrace htotal
  exact normalTracialIso_of_spatial e hδ hVN

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

universe uA uB uC uG uH uI uK uP uX uY uι uκ

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

namespace FreeGroupFactorMain.Generation

section
variable {A : Type uA} {B : Type uB} [CStarAlgebra A] [CStarAlgebra B] {ι : Type uι} {κ : Type uκ}

end

end FreeGroupFactorMain.Generation

namespace FreeGroupFactorMain

theorem normalTracialIso_of_groupEquiv {G : Type uG} {H : Type uH} [Group G] [Group H] (e : G ≃* H) :
    HasNormalTracialIso G H := by
  classical
  let ρ : G →* groupVonNeumann H := (groupUnitaryHom H).comp e.toMonoidHom
  apply normalTracialIso_of_haar_total ρ
  · intro g
    change star (groupUnitary (e g)) = groupUnitary (e g⁻¹)
    rw [map_inv]
    exact Subtype.ext (leftRegular_star (e g))
  · intro g
    change canonicalTrace (groupUnitary (e g)) = _
    rw [canonicalTrace_groupUnitary]
    simp only [e.map_eq_one_iff]
  · apply group_single_total _ (Submodule.isClosed_topologicalClosure _)
    intro h
    have hh : groupL2 (groupUnitary h) = ((ρ (e.symm h) : groupVonNeumann H) : GroupOperator H) deltaOne := by
      simp only [ρ,MonoidHom.comp_apply,MulEquiv.coe_toMonoidHom,e.apply_symm_apply]
      rfl
    rw [← groupL2_groupUnitary h,hh]
    exact Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨e.symm h,rfl⟩)

theorem HasNormalTracialIso.trans {G : Type uG} {H : Type uH} {K : Type uK} [Group G] [Group H] [Group K]
    (hGH : HasNormalTracialIso G H) (hHK : HasNormalTracialIso H K) : HasNormalTracialIso G K := by
  obtain ⟨Φ,hΦt,hΦn⟩ := hGH
  obtain ⟨Ψ,hΨt,hΨn⟩ := hHK
  refine ⟨Φ.trans Ψ,?_,?_⟩
  · intro T
    simp only [StarAlgEquiv.trans_apply,hΨt,hΦt]
  · let : TopologicalSpace (groupVonNeumann G) := groupUltraweakTopology G
    let : TopologicalSpace (groupVonNeumann H) := groupUltraweakTopology H
    let : TopologicalSpace (groupVonNeumann K) := groupUltraweakTopology K
    exact hΨn.comp hΦn

def optionRankEquiv (n : ℕ) : FreeGroup (Option (Fin n)) ≃* FreeGroupRank (n+1) :=
  FreeGroup.freeGroupCongr (finSuccEquiv n).symm

open Generation

theorem rank_step_option (n : ℕ) (hn : 3 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroup (Option (Fin n))) := by
  classical
  obtain ⟨U,htrace,htotal⟩ := generating_haar_tuple n hn
  apply normalTracialIso_of_haar_total (word U)
  · intro g
    exact (word_inv U g).symm
  · exact htrace
  · exact htotal

theorem rank_step (n : ℕ) (hn : 3 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n+1)) :=
  (rank_step_option n hn).trans (normalTracialIso_of_groupEquiv (optionRankEquiv n))

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

namespace FreeGroupFactorMain

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff

attribute [local instance] Classical.propDecidable

open UnitaryEvaluation

namespace Generation

end Generation

open Generation

theorem rank_step_option_ge_two (n : ℕ) (hn : 2 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroup (Option (Fin n))) := by
  classical
  obtain ⟨U,htrace,htotal⟩ := generating_haar_tuple_ge_two n hn
  apply normalTracialIso_of_haar_total (word U)
  · intro g
    exact (word_inv U g).symm
  · exact htrace
  · exact htotal

theorem rank_step_ge_two (n : ℕ) (hn : 2 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n+1)) :=
  (rank_step_option_ge_two n hn).trans (normalTracialIso_of_groupEquiv (optionRankEquiv n))

theorem rankTwo : HasNormalTracialIso (FreeGroupRank 2) (FreeGroupRank 3) :=
  rank_step_ge_two 2 le_rfl

theorem rankStep (n : ℕ) (hn : 3 ≤ n) :
    HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n + 1)) := rank_step n hn

end

end FreeGroupFactorMain

end OAI
end

section
namespace OAI

noncomputable section

open Set Metric Filter
open scoped NNReal Topology BigOperators ContDiff ENNReal

attribute [local instance] Classical.propDecidable

namespace FreeGroupFactorMain

namespace InfiniteGeneration

 theorem rank_three_to_index : HasNormalTracialIso (FreeGroupRank 3) Group := by
  classical
  obtain ⟨U,ht,htotal⟩ := generating_tuple
  apply normalTracialIso_of_haar_total (Generation.word U)
  · intro g
    exact (Generation.word_inv U g).symm
  · exact ht
  · exact htotal

 def indexEquivNat : Index ≃ ℕ := by
  letI : Denumerable Index := Denumerable.ofEncodableOfInfinite Index
  exact Denumerable.eqv Index

end InfiniteGeneration

theorem rankThreeInfinite : HasNormalTracialIso (FreeGroupRank 3) (FreeGroup ℕ) :=
  InfiniteGeneration.rank_three_to_index.trans
    (normalTracialIso_of_groupEquiv (FreeGroup.freeGroupCongr InfiniteGeneration.indexEquivNat))

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

namespace FreeGroupFactorMain

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36
universe u_37 u_38 u_39 u_40 u_41 u_42 u_43 u_44 u_45

namespace Amplification

section

variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

 theorem map_projection (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    IsStarProjection (Φ p) := hp.map Φ

def cornerCongr (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p) :
    Corner p hp ≃⋆ₐ[ℂ] Corner (Φ p) (map_projection Φ p hp) where
  toFun x := ⟨Φ x,by
    constructor
    · rw [← map_mul,x.property.1]
    · rw [← map_mul,x.property.2]⟩
  invFun y := ⟨Φ.symm y,by
    constructor
    · have hy := congrArg Φ.symm y.property.1
      simpa only [map_mul,Φ.symm_apply_apply] using hy
    · have hy := congrArg Φ.symm y.property.2
      simpa only [map_mul,Φ.symm_apply_apply] using hy⟩
  left_inv x := Subtype.ext (Φ.symm_apply_apply x)
  right_inv y := Subtype.ext (Φ.apply_symm_apply y)
  map_mul' x y := Subtype.ext (map_mul Φ (x : A) (y : A))
  map_add' x y := Subtype.ext (map_add Φ (x : A) (y : A))
  map_smul' z x := Subtype.ext (map_smul Φ z (x : A))
  map_star' x := Subtype.ext (map_star Φ (x : A))

end

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

 theorem cornerCongr_normal (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (hΦ : @Continuous _ _ 𝒯A 𝒯B Φ) :
    @Continuous _ _ (cornerTopology 𝒯A p hp)
      (cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)) (cornerCongr Φ p hp) := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
  let : TopologicalSpace (Corner (Φ p) (map_projection Φ p hp)) :=
    cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)
  exact (hΦ.comp continuous_subtype_val).subtype_mk _

end

open scoped ENNReal

end Amplification

namespace FreeFock
open scoped ENNReal

variable {α : Type u_15} {β : Type u_16} [DecidableEq α] [DecidableEq β]

end FreeFock
open Filter Topology

namespace Amplification

section
variable {A : Type u_17} {B : Type u_18} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_19} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

section
open scoped ENNReal ComplexConjugate
attribute [local instance] OAI.FreeGroupFactorMain.Amplification.instDecidableEqNestedHilbert

variable {I : Type u_21} {J : Type u_22}

end
section
open scoped ENNReal

variable {I : Type u_35} {J : Type u_36}

variable {G : Type u_37} [Group G]

end

section
open scoped ENNReal
variable {G : Type u_38}

variable [Group G]

end

open scoped ENNReal
variable {G : Type u_45} [Group G]

end Amplification

namespace Interpolation

open Amplification
open scoped ENNReal

def Model.Valid : Model → Prop
  | .integer n => 2≤n
  | .continuous r => 1<r
  | .infinity => True

abbrev Model.Iso (m n : Model) := NormalTracialEquiv m.trace n.trace m.topology n.topology

end Interpolation

end FreeGroupFactorMain

end

end OAI
end

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

 theorem haarSpatial_vacuum : haarSpatial (CyclicUnitary.basis (1 : FreeGroup α))=vacuum := by
  rw [haarSpatial_basis,map_one]
  rfl

end FreeFock

section

variable {A : Type u_45} {B : Type u_46} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
  [StarRing A] [StarRing B] [StarModule ℂ A] [StarModule ℂ B]

def restrictStarAlgEquiv (e : A ≃⋆ₐ[ℂ] B) (S : StarSubalgebra ℂ A) (T : StarSubalgebra ℂ B)
    (he : ∀ a,e a∈T ↔ a∈S) : S ≃⋆ₐ[ℂ] T where
  toFun a := ⟨e a,(he a).mpr a.property⟩
  invFun b := ⟨e.symm b,(he _).mp (by rw [e.apply_symm_apply]; exact b.property)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a)
  right_inv b := Subtype.ext (e.apply_symm_apply b)
  map_mul' a b := Subtype.ext (map_mul e (a : A) (b : A))
  map_add' a b := Subtype.ext (map_add e (a : A) (b : A))
  map_smul' c a := Subtype.ext (map_smul e c (a : A))
  map_star' a := Subtype.ext (map_star e (a : A))

end
open scoped ENNReal
variable {G : Type u_47} [Group G] [DecidableEq G]

namespace FreeFock
variable {α : Type u_48} [DecidableEq α]

def gaussianGroupIso : groupVonNeumann (FreeGroup α) ≃⋆ₐ[ℂ] gaussianAlgebra α :=
  restrictStarAlgEquiv haarSpatial.conjStarAlgEquiv _ _ haarSpatial_mem_vonNeumann

theorem gaussianGroupIso_trace (T : groupVonNeumann (FreeGroup α)) :
    vacuumTrace ((gaussianGroupIso T : gaussianAlgebra α) : Operator α)=canonicalTrace T := by
  have hcoe : ((gaussianGroupIso T : gaussianAlgebra α) : Operator α)=
      (haarSpatial (α := α)).conjStarAlgEquiv (T : GroupOperator (FreeGroup α)) := rfl
  rw [hcoe]
  unfold vacuumTrace
  rw [← haarSpatial_vacuum (α := α),LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,
    haarSpatial.symm_apply_apply,haarSpatial.inner_map_map]
  simp only [CyclicUnitary.basis,lp.inner_single_left,RCLike.inner_apply,map_one,mul_one]
  unfold canonicalTrace
  exact congrArg (fun ξ : GroupHilbert (FreeGroup α) => ((T : GroupOperator (FreeGroup α)) ξ) 1) (by
    ext g
    simp only [lp.single_apply,Pi.single_apply]
    split_ifs <;> rfl)

@[instance_reducible] def gaussianUltraweakTopology (α : Type u_49) [DecidableEq α] :
    TopologicalSpace (gaussianAlgebra α) :=
  TopologicalSpace.induced (fun T : gaussianAlgebra α => (T : Operator α))
    (ultraweakOperatorTopology (List α))

theorem gaussianGroupIso_normal :
    @Continuous _ _ (groupUltraweakTopology (FreeGroup α)) (gaussianUltraweakTopology α)
      (gaussianGroupIso (α := α)) := by
  let : TopologicalSpace (GroupOperator (FreeGroup α)) := ultraweakOperatorTopology (FreeGroup α)
  let : TopologicalSpace (Operator α) := ultraweakOperatorTopology (List α)
  let : TopologicalSpace (groupVonNeumann (FreeGroup α)) := groupUltraweakTopology (FreeGroup α)
  let : TopologicalSpace (gaussianAlgebra α) := gaussianUltraweakTopology α
  exact ((spatial_ultraweak_continuous haarSpatial).comp continuous_subtype_val).subtype_mk _

end FreeFock

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.HilbertUltraweak
variable (E : Type u_1) [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[instance_reducible] def topology : TopologicalSpace (E →L[ℂ] E) :=
  ⨅ (ξ : lp (fun _ : ℕ => E) 2) (η : lp (fun _ : ℕ => E) 2),
    TopologicalSpace.induced (fun T : E →L[ℂ] E => ∑' k : ℕ, inner ℂ (η k) (T (ξ k))) inferInstance

variable {E} {F : Type u_2} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

end FreeGroupFactorMain.HilbertUltraweak

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_4} [Ring A] [StarRing A]

end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.FullReducingCorner
open Amplification CornerRerouting
variable {A : Type u_5} [CStarAlgebra A]

variable (p : A) (hp : IsStarProjection p) (s : Set A)
variable (hps : p∈StarSubalgebra.centralizer ℂ s)

variable (v : A) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : p*v=v) (hvr : v*(1-p)=v) (hvi : star v*v=1-p)

end FreeGroupFactorMain.FullReducingCorner

end

namespace FreeGroupFactorMain.ReducingSubspace
variable {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
variable (K : Submodule ℂ E) [CompleteSpace K]

variable [CompleteSpace E]

end FreeGroupFactorMain.ReducingSubspace

namespace FreeGroupFactorMain.GaussianRecognition.System
open ReducingSubspace
variable {A : Type u_7} {E : Type u_8} {I : Type u_9} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)]
variable (p : M) (hp : IsStarProjection p)

variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end

variable {A : Type u_6} {B : Type u_7} [CStarAlgebra A] [CStarAlgebra B]
@[instance_reducible] def subalgebraTopology (𝒯 : TopologicalSpace A) (M : StarSubalgebra ℂ A) : TopologicalSpace M :=
  TopologicalSpace.induced (fun x : M => (x:A)) 𝒯

theorem subalgebraEquiv_normal (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a,e a∈N ↔ a∈M)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) (hn : @Continuous _ _ 𝒯A 𝒯B e) :
    @Continuous _ _ (subalgebraTopology 𝒯A M) (subalgebraTopology 𝒯B N) (subalgebraEquiv M N e he) := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace M := subalgebraTopology 𝒯A M
  exact (hn.comp continuous_subtype_val).subtype_mk _

theorem subalgebraEquiv_symm_normal (M : StarSubalgebra ℂ A) (N : StarSubalgebra ℂ B)
    (e : A ≃⋆ₐ[ℂ] B) (he : ∀ a,e a∈N ↔ a∈M)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B) (hn : @Continuous _ _ 𝒯B 𝒯A e.symm) :
    @Continuous _ _ (subalgebraTopology 𝒯B N) (subalgebraTopology 𝒯A M) (subalgebraEquiv M N e he).symm := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace N := subalgebraTopology 𝒯B N
  exact (hn.comp continuous_subtype_val).subtype_mk _

theorem subalgebraEqualityEquiv_normal (M N : StarSubalgebra ℂ A) (he : M=N) (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology 𝒯 M) (subalgebraTopology 𝒯 N) (subalgebraEqualityEquiv M N he) :=
  subalgebraEquiv_normal M N (StarAlgEquiv.refl ℂ A) _ 𝒯 𝒯 (@continuous_id A 𝒯)

theorem subalgebraEqualityEquiv_symm_normal (M N : StarSubalgebra ℂ A) (he : M=N) (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (subalgebraTopology 𝒯 N) (subalgebraTopology 𝒯 M) (subalgebraEqualityEquiv M N he).symm :=
  subalgebraEquiv_symm_normal M N (StarAlgEquiv.refl ℂ A) _ 𝒯 𝒯 (@continuous_id A 𝒯)

theorem cornerCongr_symm_normal (Φ : A ≃⋆ₐ[ℂ] B) (p : A) (hp : IsStarProjection p)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (hΦ : @Continuous _ _ 𝒯B 𝒯A Φ.symm) :
    @Continuous _ _ (cornerTopology 𝒯B (Φ p) (map_projection Φ p hp))
      (cornerTopology 𝒯A p hp) (cornerCongr Φ p hp).symm := by
  let : TopologicalSpace A := 𝒯A
  let : TopologicalSpace B := 𝒯B
  let : TopologicalSpace (Corner (Φ p) (map_projection Φ p hp)) :=
    cornerTopology 𝒯B (Φ p) (map_projection Φ p hp)
  exact (hΦ.comp continuous_subtype_val).subtype_mk _

variable (M : StarSubalgebra ℂ A) [IsClosed (M : Set A)] (p : M) (hp : IsStarProjection p)

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.FreeFock
open Amplification
variable {α : Type u_8} [DecidableEq α]

theorem gaussianGroupIso_symm_normal :
    @Continuous _ _ (gaussianUltraweakTopology α) (groupUltraweakTopology (FreeGroup α))
      (gaussianGroupIso (α := α)).symm := by
  let : TopologicalSpace (GroupOperator (FreeGroup α)) := ultraweakOperatorTopology (FreeGroup α)
  let : TopologicalSpace (Operator α) := ultraweakOperatorTopology (List α)
  let : TopologicalSpace (groupVonNeumann (FreeGroup α)) := groupUltraweakTopology (FreeGroup α)
  let : TopologicalSpace (gaussianAlgebra α) := gaussianUltraweakTopology α
  have hc := ((spatial_ultraweak_continuous (haarSpatial (α := α)).symm).comp continuous_subtype_val).subtype_mk
    (fun x : gaussianAlgebra α => ((gaussianGroupIso (α := α)).symm x).property)
  convert hc using 1 <;> rfl

def scalarGroupIso : groupVonNeumann (FreeGroup ScalarIndex) ≃⋆ₐ[ℂ] scalarSystem.generated scalarFlip :=
  gaussianGroupIso.trans (subalgebraEqualityEquiv _ _ scalar_generated_eq_gaussian.symm)

theorem scalarGroupIso_normal :
    @Continuous _ _ (groupUltraweakTopology (FreeGroup ScalarIndex)) (scalarSystem.generatedTopology scalarFlip)
      scalarGroupIso := by
  let : TopologicalSpace (groupVonNeumann (FreeGroup ScalarIndex)) := groupUltraweakTopology (FreeGroup ScalarIndex)
  let : TopologicalSpace (gaussianAlgebra ScalarIndex) := gaussianUltraweakTopology ScalarIndex
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  exact (subalgebraEqualityEquiv_normal _ _ scalar_generated_eq_gaussian.symm
    (HilbertUltraweak.topology (Fock ScalarIndex))).comp gaussianGroupIso_normal

theorem scalarGroupIso_symm_normal :
    @Continuous _ _ (scalarSystem.generatedTopology scalarFlip) (groupUltraweakTopology (FreeGroup ScalarIndex))
      scalarGroupIso.symm := by
  let : TopologicalSpace (groupVonNeumann (FreeGroup ScalarIndex)) := groupUltraweakTopology (FreeGroup ScalarIndex)
  let : TopologicalSpace (gaussianAlgebra ScalarIndex) := gaussianUltraweakTopology ScalarIndex
  let : TopologicalSpace (scalarSystem.generated scalarFlip) := scalarSystem.generatedTopology scalarFlip
  have hc := gaussianGroupIso_symm_normal.comp (subalgebraEqualityEquiv_symm_normal _ _
    scalar_generated_eq_gaussian.symm (HilbertUltraweak.topology (Fock ScalarIndex)))
  convert hc using 1 <;> rfl

theorem scalarGroupIso_trace (T : groupVonNeumann (FreeGroup ScalarIndex)) :
    scalarTrace (scalarGroupIso T)=canonicalTrace T := gaussianGroupIso_trace T
end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_9} {B : Type u_10} [CStarAlgebra A] [CStarAlgebra B]
variable (p : A) (hp : IsStarProjection p) (q : Corner p hp) (hq : IsStarProjection q)

include hq in
theorem nested_projection : IsStarProjection (q:A) :=
  ⟨congrArg Subtype.val hq.isIdempotentElem.eq,congrArg Subtype.val hq.isSelfAdjoint.star_eq⟩

theorem nested_supported (x : A) (hx : (q:A)*x=x ∧ x*(q:A)=x) : p*x=x ∧ x*p=x := by
  constructor
  · calc p*x=p*((q:A)*x) := congrArg (p*·) hx.1.symm
         _=(p*(q:A))*x := (mul_assoc _ _ _).symm
         _=x := by rw [q.property.1,hx.1]
  · calc x*p=(x*(q:A))*p := congrArg (·*p) hx.2.symm
         _=x*((q:A)*p) := mul_assoc _ _ _
         _=x := by rw [q.property.2,hx.2]

def nestedCornerEquiv : Corner q hq ≃⋆ₐ[ℂ] Corner (q:A) (nested_projection p hp q hq) where
  toFun x := ⟨x.val.val,⟨congrArg Subtype.val x.property.1,congrArg Subtype.val x.property.2⟩⟩
  invFun x := ⟨⟨x.val,nested_supported p hp q x.val x.property⟩,
    ⟨Subtype.ext x.property.1,Subtype.ext x.property.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

theorem nestedCornerEquiv_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (cornerTopology (cornerTopology 𝒯 p hp) q hq)
      (cornerTopology 𝒯 (q:A) (nested_projection p hp q hq)) (nestedCornerEquiv p hp q hq) := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
  let : TopologicalSpace (Corner q hq) := cornerTopology (cornerTopology 𝒯 p hp) q hq
  exact (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

theorem nestedCornerEquiv_symm_normal (𝒯 : TopologicalSpace A) :
    @Continuous _ _ (cornerTopology 𝒯 (q:A) (nested_projection p hp q hq))
      (cornerTopology (cornerTopology 𝒯 p hp) q hq) (nestedCornerEquiv p hp q hq).symm := by
  let : TopologicalSpace A := 𝒯
  let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
  let : TopologicalSpace (Corner (q:A) (nested_projection p hp q hq)) :=
    cornerTopology 𝒯 (q:A) (nested_projection p hp q hq)
  exact (continuous_subtype_val.subtype_mk _).subtype_mk _

variable (τ : A → ℂ) (𝒯 : TopologicalSpace A)

 theorem HasCornerScaling.mul {t s : ℝ} (ht : HasCornerScaling τ 𝒯 t)
    (hs : HasCornerScaling τ 𝒯 s) : HasCornerScaling τ 𝒯 (t*s) := by
  rcases ht with ⟨p,hp,e,hpτ,hen,hein,heτ⟩
  rcases hs with ⟨q,hq,f,hqτ,hfn,hfin,hfτ⟩
  let r : Corner p hp := e q
  have hr : IsStarProjection r := map_projection e q hq
  let g := f.trans ((cornerCongr e q hq).trans (nestedCornerEquiv p hp r hr))
  refine ⟨(r:A),nested_projection p hp r hr,g,?_,?_,?_,?_⟩
  · change τ (e q : A)=(t*s:ℝ)
    rw [heτ,hqτ,Complex.ofReal_mul]
  · let : TopologicalSpace A := 𝒯
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
    let : TopologicalSpace (Corner q hq) := cornerTopology 𝒯 q hq
    let : TopologicalSpace (Corner r hr) := cornerTopology (cornerTopology 𝒯 p hp) r hr
    exact (nestedCornerEquiv_normal p hp r hr 𝒯).comp
      ((cornerCongr_normal e q hq 𝒯 (cornerTopology 𝒯 p hp) hen).comp hfn)
  · let : TopologicalSpace A := 𝒯
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯 p hp
    let : TopologicalSpace (Corner q hq) := cornerTopology 𝒯 q hq
    let : TopologicalSpace (Corner r hr) := cornerTopology (cornerTopology 𝒯 p hp) r hr
    let : TopologicalSpace (Corner (r:A) (nested_projection p hp r hr)) :=
      cornerTopology 𝒯 (r:A) (nested_projection p hp r hr)
    exact hfin.comp ((cornerCongr_symm_normal e q hq 𝒯 (cornerTopology 𝒯 p hp) hein).comp
      (nestedCornerEquiv_symm_normal p hp r hr 𝒯))
  · intro x
    change τ (e (f x : A) : A)=((t*s:ℝ):ℂ)*τ x
    rw [heτ,hfτ,Complex.ofReal_mul,mul_assoc]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24
universe u_25 u_26 u_27 u_28 u_29 u_30 u_31

namespace FreeGroupFactorMain
namespace InfiniteICC

 theorem reduced_append_fresh {α : Type u_1} {L : List (α × Bool)} (hL : FreeGroup.IsReduced L)
    (a : α) (b : Bool) (ha : ∀ x ∈ L, x.1 ≠ a) : FreeGroup.IsReduced (L++[(a,b)]) := by
  induction L with
  | nil => exact FreeGroup.IsReduced.singleton
  | cons x L ih =>
    cases L with
    | nil =>
      rw [List.cons_append,List.nil_append,FreeGroup.isReduced_cons_cons]
      exact ⟨fun he => (ha x (by simp) he).elim,FreeGroup.IsReduced.singleton⟩
    | cons y L =>
      rw [FreeGroup.isReduced_cons_cons] at hL
      simp only [List.cons_append]
      rw [FreeGroup.isReduced_cons_cons]
      exact ⟨hL.1,ih hL.2 (fun z hz => ha z (List.mem_cons_of_mem _ hz))⟩

 theorem reduced_conjugate_fresh {α : Type u_2} {L : List (α × Bool)} (hL : FreeGroup.IsReduced L)
    (hne : L ≠ []) (a : α) (ha : ∀ x ∈ L, x.1 ≠ a) :
    FreeGroup.IsReduced ((a,true)::(L++[(a,false)])) := by
  cases L with
  | nil => exact (hne rfl).elim
  | cons x L =>
    rw [List.cons_append,FreeGroup.isReduced_cons_cons]
    refine ⟨fun he => (ha x (by simp) he.symm).elim,?_⟩
    exact reduced_append_fresh hL a false ha

 theorem conjugate_word (g : FreeGroup ℕ) (hg : g ≠ 1) (a : ℕ)
    (ha : ∀ x ∈ g.toWord, x.1 ≠ a) :
    (FreeGroup.of a*g*(FreeGroup.of a)⁻¹).toWord=
      (a,true)::(g.toWord++[(a,false)]) := by
  have he : FreeGroup.of a*g*(FreeGroup.of a)⁻¹ =
      FreeGroup.mk ((a,true)::(g.toWord++[(a,false)])) := by
    rw [← List.singleton_append,← List.append_assoc,← FreeGroup.mul_mk,← FreeGroup.mul_mk,
      FreeGroup.mk_toWord]
    rfl
  rw [he,FreeGroup.toWord_mk]
  exact (reduced_conjugate_fresh FreeGroup.isReduced_toWord (FreeGroup.toWord_eq_nil_iff.not.mpr hg) a ha).reduce_eq

 theorem infinite_conjugates (g : FreeGroup ℕ) (hg : g ≠ 1) :
    ∃ c : ℕ → FreeGroup ℕ, Function.Injective c ∧ ∀ n, ∃ a, c n=a*g*a⁻¹ := by
  classical
  let S : Finset ℕ := (g.toWord.map Prod.fst).toFinset
  let M := S.sup id
  let a (n : ℕ) := M+1+n
  have hfresh (n : ℕ) (x) (hx : x ∈ g.toWord) : x.1 ≠ a n := by
    have hm : x.1 ≤ M := Finset.le_sup (f := id) (by simpa only [S,List.mem_toFinset,List.mem_map] using ⟨x,hx,rfl⟩)
    dsimp [a]
    omega
  refine ⟨fun n => FreeGroup.of (a n)*g*(FreeGroup.of (a n))⁻¹,?_,fun n => ⟨FreeGroup.of (a n),rfl⟩⟩
  intro m n h
  have hw := congrArg FreeGroup.toWord h
  rw [conjugate_word g hg (a m) (hfresh m),conjugate_word g hg (a n) (hfresh n)] at hw
  have he : a m=a n := congrArg Prod.fst (List.cons.inj hw).1
  dsimp [a] at he
  omega

end InfiniteICC

 theorem central_coefficient_conjugate {G : Type u_3} [Group G] [DecidableEq G]
    (T : groupVonNeumann G) (hT : ∀ S : groupVonNeumann G, Commute T S) (a g : G) :
    ((T : GroupOperator G) deltaOne) (a*g*a⁻¹)=((T : GroupOperator G) deltaOne) g := by
  have he : (T : GroupOperator G)*leftRegular a=leftRegular a*(T : GroupOperator G) :=
    congrArg (fun A : groupVonNeumann G => (A : GroupOperator G)) (hT (groupUnitary a)).eq
  have hd : leftRegular a deltaOne=lp.single 2 a 1 := by
    ext x
    simp [leftRegular_apply,deltaOne,lp.single_apply,Pi.single_apply,inv_mul_eq_one,eq_comm]
  have hx := congrArg (fun A : GroupOperator G => A deltaOne (a*g)) he
  simp only [mul_apply_eq_comp,hd,leftRegular_apply,inv_mul_cancel_left] at hx
  rw [groupVN_matrix] at hx
  exact hx

 theorem group_center_scalar_of_infinite_conjugates {G : Type u_4} [Group G]
    (hICC : ∀ g : G, g ≠ 1 → ∃ c : ℕ → G, Function.Injective c ∧ ∀ n, ∃ a, c n=a*g*a⁻¹)
    (T : groupVonNeumann G) (hT : ∀ S : groupVonNeumann G, Commute T S) :
    T=canonicalTrace T • (1 : groupVonNeumann G) := by
  classical
  have hz (g : G) (hg : g ≠ 1) : ((T : GroupOperator G) deltaOne) g=0 := by
    obtain ⟨c,hc,hconj⟩ := hICC g hg
    have hs : Summable (fun x : G => ‖((T : GroupOperator G) deltaOne) x‖^2) := by
      simpa only [ENNReal.toReal_ofNat,Real.rpow_two] using
        (lp.memℓp ((T : GroupOperator G) deltaOne)).summable (by norm_num)
    have hcst : Summable (fun _ : ℕ => ‖((T : GroupOperator G) deltaOne) g‖^2) := by
      have hh := hs.comp_injective hc
      change Summable (fun n : ℕ => ‖((T : GroupOperator G) deltaOne) (c n)‖^2) at hh
      have he : (fun n : ℕ => ‖((T : GroupOperator G) deltaOne) (c n)‖^2) =
          (fun _ : ℕ => ‖((T : GroupOperator G) deltaOne) g‖^2) := by
        funext n
        obtain ⟨a,ha⟩ := hconj n
        rw [ha,central_coefficient_conjugate T hT]
      rwa [he] at hh
    have hh := (summable_const_iff _).mp hcst
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg (((T : GroupOperator G) deltaOne) g)])
  apply sub_eq_zero.mp
  apply groupVN_separating
  rw [← deltaOne_eq]
  ext g
  change ((T : GroupOperator G) deltaOne) g-canonicalTrace T*deltaOne g=(0 : ℂ)
  by_cases hg : g=1
  · subst g
    simp only [deltaOne,lp.single_apply,Pi.single_eq_same,mul_one,canonicalTrace]
    exact sub_self _
  · rw [hz g hg]
    simp [deltaOne,lp.single_apply,hg]

 theorem infinite_free_group_center_scalar (T : groupVonNeumann (FreeGroup ℕ))
    (hT : ∀ S : groupVonNeumann (FreeGroup ℕ), Commute T S) :
    T=canonicalTrace T • (1 : groupVonNeumann (FreeGroup ℕ)) :=
  group_center_scalar_of_infinite_conjugates InfiniteICC.infinite_conjugates T hT

end FreeGroupFactorMain

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_9} [CStarAlgebra A]

end
section
open scoped ENNReal ComplexConjugate

variable {I : Type u_11} {J : Type u_12}
end
section
open scoped ENNReal

variable {I : Type u_14} {J : Type u_15}

variable {G : Type u_16} [Group G]

end
section
open scoped ENNReal
variable {I : Type u_17} {J : Type u_18}

variable {G : Type u_21} [Group G]

end
section
variable {I : Type u_22} {J : Type u_23}

 variable {G : Type u_28} [Group G]

end
open scoped ENNReal
variable {I : Type u_29} {J : Type u_30}

 variable {G : Type u_31} [Group G] [DecidableEq G]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

def unitCornerEquiv : A ≃⋆ₐ[ℂ] Corner (1:A) (IsStarProjection.one A) where
  toFun a := ⟨a,⟨one_mul a,mul_one a⟩⟩
  invFun a := a.val
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  map_star' _ := rfl

 theorem HasCornerScaling.one (τ : A → ℂ) (𝒯 : TopologicalSpace A) (hτ : τ 1=1) :
    HasCornerScaling τ 𝒯 1 := by
  refine ⟨1,(IsStarProjection.one A),unitCornerEquiv,?_,?_,?_,?_⟩
  · simpa only [Complex.ofReal_one] using hτ
  · let : TopologicalSpace A := 𝒯
    exact continuous_id.subtype_mk _
  · let : TopologicalSpace A := 𝒯
    exact continuous_subtype_val
  · intro x
    change τ x=(1:ℂ)*τ x
    rw [one_mul]

 theorem HasCornerScaling.pow (τ : A → ℂ) (𝒯 : TopologicalSpace A) (hτ : τ 1=1)
    {t : ℝ} (ht : HasCornerScaling τ 𝒯 t) (n : ℕ) : HasCornerScaling τ 𝒯 (t^n) := by
  induction n with
  | zero => simpa only [pow_zero] using HasCornerScaling.one τ 𝒯 hτ
  | succ n ih => simpa only [pow_succ] using ih.mul τ 𝒯 ht

 theorem HasCornerScaling.of_near_one (τ : A → ℂ) (𝒯 : TopologicalSpace A) (hτ : τ 1=1)
    (hnear : ∀ t : ℝ,1/2<t → t<1 → HasCornerScaling τ 𝒯 t)
    (t : ℝ) (ht : 0<t) (ht1 : t≤1) : HasCornerScaling τ 𝒯 t := by
  rcases lt_or_eq_of_le ht1 with ht1 | rfl
  swap
  · exact HasCornerScaling.one τ 𝒯 hτ
  obtain ⟨n,hn⟩ := exists_pow_lt_of_lt_one ht (by norm_num : (1/2:ℝ)<1)
  have hn0 : n≠0 := by
    intro hn0
    rw [hn0,pow_zero] at hn
    exact (lt_irrefl (1:ℝ)) (hn.trans ht1)
  let r : ℝ := t^((n:ℝ)⁻¹)
  have hr0 : 0≤r := Real.rpow_nonneg ht.le _
  have hrpow : r^n=t := Real.rpow_inv_natCast_pow ht.le hn0
  have hrhalf : 1/2<r := by
    by_contra h
    have hh := pow_le_pow_left₀ hr0 (le_of_not_gt h) n
    rw [hrpow] at hh
    exact (not_le_of_gt hn) hh
  have hr1 : r<1 := Real.rpow_lt_one ht.le ht1 (inv_pos.mpr (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0)))
  have h := HasCornerScaling.pow τ 𝒯 hτ (hnear r hrhalf hr1) n
  rwa [hrpow] at h

 theorem HasCornerScaling.transport (τA : A → ℂ) (τB : B → ℂ)
    (𝒯A : TopologicalSpace A) (𝒯B : TopologicalSpace B)
    (e : A ≃⋆ₐ[ℂ] B) (hn : @Continuous _ _ 𝒯A 𝒯B e)
    (hin : @Continuous _ _ 𝒯B 𝒯A e.symm) (hτ : ∀x,τB (e x)=τA x)
    {t : ℝ} (ht : HasCornerScaling τA 𝒯A t) : HasCornerScaling τB 𝒯B t := by
  rcases ht with ⟨p,hp,f,hpτ,hfn,hfin,hfτ⟩
  let g := e.symm.trans (f.trans (cornerCongr e p hp))
  refine ⟨e p,map_projection e p hp,g,?_,?_,?_,?_⟩
  · rw [hτ,hpτ]
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    exact ((cornerCongr_normal e p hp 𝒯A 𝒯B hn).comp hfn).comp hin
  · let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace (Corner p hp) := cornerTopology 𝒯A p hp
    let : TopologicalSpace (Corner (e p) (map_projection e p hp)) := cornerTopology 𝒯B (e p) (map_projection e p hp)
    exact hn.comp (hfin.comp (cornerCongr_symm_normal e p hp 𝒯A 𝒯B hin))
  · intro x
    change τB (e (f (e.symm x) : A))=(t:ℂ)*τB x
    rw [hτ,hfτ,←hτ,StarAlgEquiv.apply_symm_apply]
end

variable {A : Type u_3} {B : Type u_4} [CStarAlgebra A] [CStarAlgebra B]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition

 theorem scalar_hasCornerScaling_near_one (t : ℝ) (ht : 1/2<t) (ht1 : t<1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) t := by
  have ht0 : 0<t := by linarith
  have hs0 : 0<1-t := sub_pos.mpr ht1
  have hv : 0<Real.sqrt (1-t) := Real.sqrt_pos.mpr hs0
  have hvu : Real.sqrt (1-t)<Real.sqrt t := Real.sqrt_lt_sqrt hs0.le (by linarith)
  have ht2 := Real.sq_sqrt ht0.le
  have hs2 := Real.sq_sqrt hs0.le
  have hunit : (Real.sqrt t)^2+(Real.sqrt (1-t))^2=1 := by rw [ht2,hs2]; ring
  have hh := scalar_hasCornerScaling_weighted (Real.sqrt t) (Real.sqrt (1-t)) hv hvu hunit
  rwa [ht2] at hh

 theorem scalarTrace_one : scalarTrace 1=1 := by
  exact FreeFock.vacuumTrace_one

 theorem scalar_hasCornerScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling scalarTrace (scalarSystem.generatedTopology scalarFlip) t :=
  HasCornerScaling.of_near_one scalarTrace (scalarSystem.generatedTopology scalarFlip)
    scalarTrace_one scalar_hasCornerScaling_near_one t ht ht1

 theorem scalarGroup_hasCornerScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling (canonicalTrace (G := FreeGroup ScalarIndex))
      (groupUltraweakTopology (FreeGroup ScalarIndex)) t := by
  apply HasCornerScaling.transport scalarTrace canonicalTrace
    (scalarSystem.generatedTopology scalarFlip) (groupUltraweakTopology (FreeGroup ScalarIndex))
    scalarGroupIso.symm scalarGroupIso_symm_normal scalarGroupIso_normal
    (fun T => ?_) (scalar_hasCornerScaling t ht ht1)
  simpa only [StarAlgEquiv.apply_symm_apply] using (scalarGroupIso_trace (scalarGroupIso.symm T)).symm
end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
open WeightedFock FreeFock

theorem smallScaling_transport_group {G : Type u_6} {H : Type u_7} [Group G] [Group H]
    (h : HasNormalTracialIso G H) {t : ℝ}
    (ht : HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t) :
    HasCornerScaling (canonicalTrace (G := H)) (groupUltraweakTopology H) t := by
  classical
  obtain ⟨Φ,hΦ,_⟩ := h
  obtain ⟨e,hδ,he⟩ := spatial_of_trace_iso Φ hΦ
  apply HasCornerScaling.transport canonicalTrace canonicalTrace
    (groupUltraweakTopology G) (groupUltraweakTopology H)
    (spatialGroupIso e he) (spatialGroupIso_normal e he) (spatialGroupIso_symm_normal e he) ?_ ht
  intro T
  rw [canonicalTrace_eq_inner,canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne)))=_
  rw [←hδ,e.symm_apply_apply,e.inner_map_map]

theorem infinite_hasCornerScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling (canonicalTrace (G := FreeGroup ℕ))
      (groupUltraweakTopology (FreeGroup ℕ)) t := by
  classical
  let : Denumerable ScalarIndex := Denumerable.ofEncodableOfInfinite ScalarIndex
  let e : ScalarIndex ≃ ℕ := (Denumerable.eqv ScalarIndex)
  exact smallScaling_transport_group (normalTracialIso_of_groupEquiv (FreeGroup.freeGroupCongr e))
    (scalarGroup_hasCornerScaling t ht ht1)
end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification

section
variable {A : Type u_1} {B : Type u_2} {C : Type u_3} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

namespace NormalTracialEquiv
variable {τA : A → ℂ} {τB : B → ℂ} {τC : C → ℂ}
variable {𝒯A : TopologicalSpace A} {𝒯B : TopologicalSpace B} {𝒯C : TopologicalSpace C}

def symm (e : NormalTracialEquiv τA τB 𝒯A 𝒯B) : NormalTracialEquiv τB τA 𝒯B 𝒯A where
  equiv := e.equiv.symm
  trace_eq x := by simpa only [StarAlgEquiv.apply_symm_apply] using (e.trace_eq (e.equiv.symm x)).symm
  normal := e.inverse_normal
  inverse_normal := e.normal

def trans (e : NormalTracialEquiv τA τB 𝒯A 𝒯B) (f : NormalTracialEquiv τB τC 𝒯B 𝒯C) :
    NormalTracialEquiv τA τC 𝒯A 𝒯C where
  equiv := e.equiv.trans f.equiv
  trace_eq x := (f.trace_eq (e.equiv x)).trans (e.trace_eq x)
  normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact f.normal.comp e.normal
  inverse_normal := by
    let : TopologicalSpace A := 𝒯A
    let : TopologicalSpace B := 𝒯B
    let : TopologicalSpace C := 𝒯C
    exact e.inverse_normal.comp f.inverse_normal

end NormalTracialEquiv
end

open scoped ENNReal
variable {G : Type u_4} [Group G]

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

theorem allPositiveScaling_both
    (hbase : ∀ T : groupVonNeumann G, (∀ S : groupVonNeumann G,Commute T S) →
      ∃ c : ℂ,T=c • (1 : groupVonNeumann G))
    (hsmall : ∀t : ℝ,0<t → t≤1 → HasCornerScaling (canonicalTrace (G := G)) (groupUltraweakTopology G) t)
    (t : ℝ) (ht : 0<t) :
    (∃p : stabilization G,IsStarProjection p ∧ stabilizedProjectionTrace p=ENNReal.ofReal t) ∧
    ∀(p : stabilization G)(hp : IsStarProjection p),stabilizedProjectionTrace p=ENNReal.ofReal t →
      Nonempty (GroupCornerNormalIso t p hp) := by
  obtain ⟨q,hq,hqτ,⟨E⟩⟩ := preferred_scaling_model (G := G) hbase hsmall t ht
  refine ⟨⟨q,hq,hqτ⟩,?_⟩
  intro p hp hpτ
  obtain ⟨f,hfτ,hfn,hfin⟩ := finite_corner_choice_both (G := G) hbase t p q hp hq
    (hpτ.trans hqτ.symm) (hpτ ▸ ENNReal.ofReal_ne_top)
  let F : NormalTracialEquiv (normalizedCornerTrace stabilizedTrace t p hp)
      (normalizedCornerTrace stabilizedTrace t q hq)
      (cornerTopology (stabilizationTopology G) p hp) (cornerTopology (stabilizationTopology G) q hq) :=
    ⟨f,hfτ,hfn,hfin⟩
  exact ⟨F.trans E⟩

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain

theorem HasNormalTracialIso.symm {G : Type u_2} {H : Type u_3} [Group G] [Group H]
    (h : HasNormalTracialIso G H) : HasNormalTracialIso H G := by
  classical
  obtain ⟨Φ,hΦ,_⟩ := h
  obtain ⟨e,hδ,he⟩ := Amplification.spatial_of_trace_iso Φ hΦ
  refine ⟨(spatialGroupIso e he).symm,?_,spatialGroupIso_symm_normal e he⟩
  intro T
  rw [canonicalTrace_eq_inner,canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e.symm ((T : GroupOperator H) (e deltaOne)))=_
  rw [hδ,←e.inner_map_map,e.apply_symm_apply,hδ]

theorem center_scalar_of_iso {G : Type u_4} {H : Type u_5} [Group G] [Group H]
    (e : groupVonNeumann G ≃⋆ₐ[ℂ] groupVonNeumann H)
    (hH : ∀ T : groupVonNeumann H,(∀ S : groupVonNeumann H,Commute T S) → ∃ c : ℂ,T=c • 1)
    (T : groupVonNeumann G) (hT : ∀ S : groupVonNeumann G,Commute T S) :
    ∃ c : ℂ,T=c • 1 := by
  have he : ∀ S : groupVonNeumann H,Commute (e T) S := by
    intro S
    have hh := (hT (e.symm S)).map e
    simpa only [StarAlgEquiv.apply_symm_apply] using hh
  obtain ⟨c,hc⟩ := hH (e T) he
  have hec : e (c • (1 : groupVonNeumann G))=c • (1 : groupVonNeumann H) := by
    change e.toFun (c • (1 : groupVonNeumann G))=_
    rw [e.map_smul']
    change c • e (1 : groupVonNeumann G)=_
    rw [map_one]
  exact ⟨c,e.injective (hc.trans hec.symm)⟩

end FreeGroupFactorMain
namespace FreeGroupFactorMain.Amplification
open scoped ENNReal

theorem rankTwo_smallScaling (t : ℝ) (ht : 0<t) (ht1 : t≤1) :
    HasCornerScaling (canonicalTrace (G := FreeGroupRank 2)) (groupUltraweakTopology (FreeGroupRank 2)) t :=
  smallScaling_transport_group ((rankTwo.trans rankThreeInfinite).symm) (infinite_hasCornerScaling t ht ht1)

theorem rankTwo_center_scalar (T : groupVonNeumann (FreeGroupRank 2))
    (hT : ∀ S : groupVonNeumann (FreeGroupRank 2),Commute T S) : ∃c : ℂ,T=c • 1 := by
  obtain ⟨e,_,_⟩ := rankTwo.trans rankThreeInfinite
  exact center_scalar_of_iso e (fun S hS => ⟨canonicalTrace S,infinite_free_group_center_scalar S hS⟩) T hT

theorem rankTwo_allPositiveScaling (t : ℝ) (ht : 0<t) :
    (∃p : stabilization (FreeGroupRank 2),IsStarProjection p ∧ stabilizedProjectionTrace p=ENNReal.ofReal t) ∧
    ∀(p : stabilization (FreeGroupRank 2))(hp : IsStarProjection p),stabilizedProjectionTrace p=ENNReal.ofReal t →
      Nonempty (GroupCornerNormalIso t p hp) :=
  allPositiveScaling_both rankTwo_center_scalar rankTwo_smallScaling t ht

end FreeGroupFactorMain.Amplification

end

end OAI
end

section
namespace OAI

universe u_1 u_2 u_3

noncomputable section
namespace FreeGroupFactorMain.Amplification
variable {G : Type u_1} {H : Type u_2} [Group G] [Group H]

theorem groupNormal_of_iso (h : HasNormalTracialIso G H) :
    Nonempty (NormalTracialEquiv (canonicalTrace (G := G)) (canonicalTrace (G := H))
      (groupUltraweakTopology G) (groupUltraweakTopology H)) := by
  classical
  obtain ⟨Φ,hΦ,_⟩ := h
  obtain ⟨e,hδ,he⟩ := spatial_of_trace_iso Φ hΦ
  refine ⟨⟨spatialGroupIso e he,?_,spatialGroupIso_normal e he,spatialGroupIso_symm_normal e he⟩⟩
  intro T
  rw [canonicalTrace_eq_inner,canonicalTrace_eq_inner]
  change inner ℂ deltaOne (e ((T : GroupOperator G) (e.symm deltaOne)))=_
  rw [←hδ,e.symm_apply_apply,e.inner_map_map]

end FreeGroupFactorMain.Amplification
namespace FreeGroupFactorMain

theorem groupIso_refl (G : Type u_3) [Group G] : HasNormalTracialIso G G :=
  ⟨StarAlgEquiv.refl ℂ (groupVonNeumann G),fun _ => rfl,@continuous_id _ (groupUltraweakTopology G)⟩

theorem finiteRank_to_two (n : ℕ) (hn : 2≤n) : HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank 2) := by
  induction n, hn using Nat.le_induction with
  | base => exact groupIso_refl _
  | succ n hn ih =>
    have he : HasNormalTracialIso (FreeGroupRank n) (FreeGroupRank (n+1)) := by
      rcases eq_or_lt_of_le hn with h | h
      · subst n
        exact rankTwo
      · exact rankStep n (by omega)
    exact he.symm.trans ih

end FreeGroupFactorMain

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1

namespace FreeGroupFactorMain.Interpolation
open Amplification
open scoped ENNReal

theorem selectedProjection_trace (a : ℝ) (ha : 0<a) :
    stabilizedProjectionTrace (selectedProjection a).val=ENNReal.ofReal a := by
  unfold selectedProjection
  apply Classical.epsilon_spec (p := fun p : RankTwoProjection => stabilizedProjectionTrace p.val=ENNReal.ofReal a)
  obtain ⟨p,hp,ht⟩ := (rankTwo_allPositiveScaling a ha).1
  exact ⟨⟨p,hp⟩,ht⟩

theorem interpolationScale_pos (r : ℝ) (hr : 1<r) : 0 < interpolationScale r :=
  inv_pos.mpr (Real.sqrt_pos.mpr (sub_pos.mpr hr))

theorem Model.toRankTwo (m : Model) (hm : m.Valid) :
    Nonempty (NormalTracialEquiv m.trace (canonicalTrace (G := FreeGroupRank 2))
      m.topology (groupUltraweakTopology (FreeGroupRank 2))) := by
  cases m with
  | integer n => exact groupNormal_of_iso (finiteRank_to_two n hm)
  | continuous r =>
    exact (rankTwo_allPositiveScaling _ (interpolationScale_pos r hm)).2 _ _
      (selectedProjection_trace _ (interpolationScale_pos r hm))
  | infinity => exact groupNormal_of_iso (rankTwo.trans rankThreeInfinite).symm

theorem Model.allIsomorphic (m n : Model) (hm : m.Valid) (hn : n.Valid) :
    Nonempty (m.Iso n) := by
  obtain ⟨E⟩ := m.toRankTwo hm
  obtain ⟨F⟩ := n.toRankTwo hn
  exact ⟨E.trans F.symm⟩

theorem parameterModel_nonnatural (r : ℝ≥0∞) (hrtop : r≠⊤)
    (hrnat : ¬∃n : ℕ,r=(n:ℝ≥0∞)) : parameterModel r=Model.continuous r.toReal := by
  classical
  simp only [parameterModel,ite_eq_right hrtop,dite_eq_right hrnat]

theorem parameterModel_valid (r : ℝ≥0∞) (hr : 1<r) : (parameterModel r).Valid := by
  classical
  by_cases htop : r=⊤
  · rw [htop,parameterModel_top]
    trivial
  · by_cases hn : ∃n : ℕ,r=(n:ℝ≥0∞)
    · obtain ⟨n,rfl⟩ := hn
      rw [parameterModel_nat]
      change 2≤n
      have h : (1:ℕ)<n := by exact_mod_cast hr
      omega
    · rw [parameterModel_nonnatural r htop hn]
      change 1<r.toReal
      have h := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top htop).mpr hr
      simpa only [ENNReal.toReal_one] using h

theorem allInterpolatedIsomorphic (r s : ℝ≥0∞) (hr : 1<r) (hs : 1<s) :
    Nonempty (NormalTracialEquiv (interpolatedTrace r) (interpolatedTrace s)
      (interpolatedTopology r) (interpolatedTopology s)) :=
  Model.allIsomorphic _ _ (parameterModel_valid r hr) (parameterModel_valid s hs)

end FreeGroupFactorMain.Interpolation

namespace FreeGroupFactorMain.Amplification
open scoped ENNReal
variable {G : Type u_1} [Group G]

variable [DecidableEq G]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.Interpolation
open Amplification
open scoped ENNReal

end FreeGroupFactorMain.Interpolation

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.Interpolation.allInterpolatedIsomorphic := @OAI.FreeGroupFactorMain.Interpolation.allInterpolatedIsomorphic
