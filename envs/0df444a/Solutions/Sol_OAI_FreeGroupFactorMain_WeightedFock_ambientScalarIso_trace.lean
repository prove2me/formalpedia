-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.WeightedFock.ambientScalarIso_trace
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:11:35.281999+00:00
-- url     : https://prove2.me/submissions/f219aea2-0112-4511-954b-2af46156fa56

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

section
namespace FreeGroupFactorMain.GramSpatial
variable {I : Type u_1} {E : Type u_2} {F : Type u_3}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem spatial_trace (x : I → E) (y : I → F)
    (hg : ∀ i j, inner ℂ (y i) (y j)=inner ℂ (x i) (x j))
    (hx : (Submodule.span ℂ (Set.range x)).topologicalClosure=⊤)
    (hy : (Submodule.span ℂ (Set.range y)).topologicalClosure=⊤)
    (i₀ : I) (T : E →L[ℂ] E) :
    inner ℂ (y i₀) ((spatial x y hg hx hy).conjStarAlgEquiv T (y i₀))=
      inner ℂ (x i₀) (T (x i₀)) := by
  let W := spatial x y hg hx hy
  have he : W (x i₀)=y i₀ := spatial_family x y hg hx hy i₀
  rw [← he,LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,W.symm_apply_apply,
    W.inner_map_map]

end FreeGroupFactorMain.GramSpatial
namespace FreeGroupFactorMain.GaussianRecognition
variable (A : Type u_4) (E : Type u_5) (I : Type u_6) [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

variable {A E I} {covariance : I → I → A → A}
variable (X : System A E I covariance)

namespace System

variable {F : Type u_9} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
variable (Y : System A F I covariance)

variable
  (hstate : ∀ a, inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

theorem spatial_trace (T : Operator E) :
    inner ℂ Y.root ((spatial X Y hstate hX hY).conjStarAlgEquiv T Y.root)=
      inner ℂ X.root (T X.root) := by
  have h := GramSpatial.spatial_trace X.family Y.family
    (fun w z => normal_inner_eq X Y hstate w.1 z.1 w.2 z.2) hX hY (1,[]) T
  simpa only [spatial,family,normal,map_one,one_apply_eq_self] using h

end System
end FreeGroupFactorMain.GaussianRecognition

end

namespace FreeGroupFactorMain.GaussianRecognition
open CyclicSpectral

end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification CyclicSpectral GaussianRecognition WeightedCornerIndex

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10

namespace FreeGroupFactorMain.GaussianRecognition
section Algebraic
variable {A : Type u_1} {B : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
  [Ring B] [StarRing B] [Algebra ℂ B] [StarModule ℂ B]

end Algebraic

variable {E : Type u_3} {F : Type u_4}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

namespace System
variable {A : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable {covariance : I → I → A → A}
variable (X : System A E I covariance) (Y : System A F I covariance)
variable
  (hstate : ∀ a,inner ℂ Y.root (Y.coeff a Y.root)=inner ℂ X.root (X.coeff a X.root))
  (hX : (Submodule.span ℂ (Set.range X.family)).topologicalClosure=⊤)
  (hY : (Submodule.span ℂ (Set.range Y.family)).topologicalClosure=⊤)

theorem generatedIso_trace (σ : I → I) (T : X.generated σ) :
    inner ℂ Y.root ((X.generatedIso Y hstate hX hY σ T : Operator F) Y.root)=
      inner ℂ X.root ((T : Operator E) X.root) :=
  X.spatial_trace Y hstate hX hY (T : Operator E)

end System
end FreeGroupFactorMain.GaussianRecognition

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_8} {E : Type u_9} {I : Type u_10} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

end FreeGroupFactorMain.GaussianRecognition.System

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock MeasureTheory CyclicSpectral
variable {ι : Type u_1} [DecidableEq ι]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock WeightedCornerIndex GaussianRecognition CyclicSpectral

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock CyclicSpectral GaussianRecognition Filter Topology
open scoped ENNReal
variable {ι : Type u_2} [DecidableEq ι]

variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

section
open FreeFock WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

end

open FreeFock GaussianRecognition CyclicSpectral
variable (u v : ℝ) (hu : u≠0) (hv : v≠0) (hunit : u^2+v^2=1)

theorem ambientGaussianIso_trace (T : (ambientSystem u v hu hv hunit).generated scalarFlip) :
    inner ℂ scalarSystem.root ((ambientGaussianIso u v hu hv hunit T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      vacuumTrace u v (T:Operator ℕ) :=
  (ambientSystem u v hu hv hunit).generatedIso_trace scalarSystem
    (scalar_ambient_state u v hu hv hunit)
    (ambientSystem_total u v hu hv hunit) scalarSystem_total scalarFlip T
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section
namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

variable (hu : u≠0) (hv' : v≠0) (hunit : u^2+v^2=1)

theorem ambientScalarIso_trace (T : ambientAlgebra (ι := ℕ) u v) :
    inner ℂ scalarSystem.root ((ambientScalarIso u v hu hv' hunit T : FreeFock.Operator ScalarIndex) scalarSystem.root)=
      vacuumTrace u v (T:Operator ℕ) :=
  ambientGaussianIso_trace u v hu hv' hunit _
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.WeightedFock.ambientScalarIso_trace := @OAI.FreeGroupFactorMain.WeightedFock.ambientScalarIso_trace
