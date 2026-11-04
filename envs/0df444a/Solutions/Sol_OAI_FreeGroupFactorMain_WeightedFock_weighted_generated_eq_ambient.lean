-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.WeightedFock.weighted_generated_eq_ambient
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:13:42.812238+00:00
-- url     : https://prove2.me/submissions/dbc73647-d910-4774-b795-b1a337f131ea

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_representedAmbient_le_weightedGenerated

set_option linter.all false

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

end
section
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end

open FreeFock
variable {ι : Type u_3} [DecidableEq ι]

theorem supportedCreation_paired (u v : ℝ) (i n : ι) (r s : Bool) :
    supportedCreation u v i n r s+star (supportedCreation u v i n s r)=
      supportedLeg u v i r*S u v n*star (supportedLeg u v i s) := by
  simp only [supportedCreation,S_eq,star_mul,star_star,mul_add,add_mul,mul_assoc]

theorem normalizedCreation_paired_mem (u v : ℝ) (i n : ι) (r s : Bool) :
    normalizedCreation u v i n r s+star (normalizedCreation u v i n s r)∈ambientAlgebra u v := by
  simp only [normalizedCreation,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
  ← smul_add (M := ℂ) (A := Operator ι)]
  rw [supportedCreation_paired]
  exact (ambientAlgebra u v).smul_mem
    (mul_mem (mul_mem (supportedLeg_mem_ambient u v i r) (S_mem_ambient u v n))
      (star_mem (supportedLeg_mem_ambient u v i s))) _
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_1} [DecidableEq ι]

def residualPair (u v : ℝ) (i j : ι) (r s : Option Bool) : Operator ι :=
  residualCreation u v i j r s+star (residualCreation u v i j s r)

theorem residualPair_eq (u v : ℝ) (i j : ι) (r s : Option Bool) :
    residualPair u v i j r s=residualLeg u v i r*S u v j*star (residualLeg u v i s) := by
  simp only [residualPair,residualCreation,S_eq,star_mul,star_star,mul_add,add_mul,mul_assoc]

theorem residualPair_mem_ambient (u v : ℝ) (i j : ι) (r s : Option Bool) :
    residualPair u v i j r s∈ambientAlgebra u v := by
  rw [residualPair_eq]
  exact mul_mem (mul_mem (edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i r))
    (S_mem_ambient u v j)) (star_mem (edgeAlgebra_le_ambient u v i (residualLeg_mem_edge u v i s)))

theorem normalizedResidual_paired_mem (u v : ℝ) (i j : ι) (r s : Option Bool) :
    normalizedResidual u v i j r s+star (normalizedResidual u v i j s r)∈ambientAlgebra u v := by
  simp only [normalizedResidual,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    ← smul_add (M := ℂ) (A := Operator ι)]
  exact (ambientAlgebra u v).smul_mem (residualPair_mem_ambient u v i j r s) _

end FreeGroupFactorMain.WeightedFock

section
namespace FreeGroupFactorMain.GaussianExtension
variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (B : StarSubalgebra ℂ (E →L[ℂ] E)) (D : E →L[ℂ] E)
variable (κ : B → B) (hκ : ∀ a : B,star D*(a : E →L[ℂ] E)*D=(κ a : E →L[ℂ] E))

end FreeGroupFactorMain.GaussianExtension

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

variable {B : StarSubalgebra ℂ A} {L R : A}

end FreeGroupFactorMain.GaussianOrthogonal
namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_4} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.GaussianOrthogonal
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {B : StarSubalgebra ℂ A} {L R : A}

end FreeGroupFactorMain.GaussianOrthogonal

namespace FreeGroupFactorMain.WeightedFock
open FreeFock GaussianOrthogonal
variable {ι : Type u_6} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

section
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_1} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification CyclicSpectral
variable {ι : Type u_3} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end

section
open FreeFock Amplification WeightedCornerIndex
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

variable {ι : Type u_4} [DecidableEq ι]

theorem vertex_C_vertex (i : ι) (r : Bool) :
    vertex r*C u v i*vertex r=(weight u v r:ℂ) • edgeCreation i r r := by
  cases r
  · simp only [vertex,Bool.false_eq_true,ite_false,C,sub_mul,one_mul,mul_add,mul_smul_comm,
      P_creation_true,P_creation_false,sub_self,smul_zero,sub_zero,zero_add,
      smul_mul_assoc,weight,edgeCreation]
  · simp only [vertex,ite_true,C,mul_add,mul_smul_comm,P_creation_true,
      P_creation_false,smul_zero (M := ℂ) (A := Operator ι),add_zero,smul_mul_assoc,weight,edgeCreation]

theorem pDiagonal_eq_pFresh (i : ι) (r : Bool) :
    pDiagonal u v i i r=pFresh u v i i r r := by
  apply Subtype.ext
  change ((weight u v (!r):ℂ)/(u:ℂ)) •
    (supportedLeg u v i r*edgeCreation i (!r) (!r)*star (supportedLeg u v i r))=
      (u:ℂ)⁻¹ • (supportedLeg u v i r*C u v i*star (supportedLeg u v i r))
  have hh : supportedLeg u v i r*C u v i*star (supportedLeg u v i r)=
      (weight u v (!r):ℂ) •
        (supportedLeg u v i r*edgeCreation i (!r) (!r)*star (supportedLeg u v i r)) := by
    calc
      _ = supportedLeg u v i r*(vertex (!r)*C u v i*vertex (!r))*star (supportedLeg u v i r) := by
        simp only [← mul_assoc,supportedLeg_vertex]
        rw [mul_assoc _ (vertex (!r)),vertex_star_supportedLeg]
      _ = _ := by rw [vertex_C_vertex];simp only [mul_smul_comm,smul_mul_assoc]
  rw [hh,smul_smul]
  congr 1
  exact div_eq_inv_mul _ _
end

section
open FreeFock Amplification WeightedCornerIndex
variable {ι : Type u_5} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)
variable (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)

end

open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable {ι : Type u_6} [DecidableEq ι]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

 theorem compress_mul_corner (p : A) (hp : IsStarProjection p) (B : A) (hB : Commute p B)
    (a : Corner p hp) : (p*B*p)*(a:A)=B*(a:A) := by
  rw [mul_assoc _ p,a.property.1,hB.eq,mul_assoc,a.property.1]

 theorem corner_mul_compress (p : A) (hp : IsStarProjection p) (B : A) (hB : Commute p B)
    (a : Corner p hp) : (a:A)*(p*B*p)=(a:A)*B := by
  calc
    _ = ((a:A)*p)*(B*p) := by simp only [mul_assoc]
    _ = (a:A)*(p*B) := by rw [a.property.2,← hB.eq]
    _ = _ := by rw [← mul_assoc,a.property.2]

 theorem relative_corner_bicommutant (s : Set A) (p : A) (hp : IsStarProjection p)
    (hpM : p∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A)) :
    StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ
        (subalgebraCorner (StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ s : Set A)) p hp hpM : Set (Corner p hp)) : Set (Corner p hp)) ≤
      subalgebraCorner (StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A)) p hp hpM := by
  intro a ha
  change (a:A)∈StarSubalgebra.centralizer ℂ (StarSubalgebra.centralizer ℂ s : Set A)
  rw [StarSubalgebra.mem_centralizer_iff]
  have htest (B : A) (hB : B∈StarSubalgebra.centralizer ℂ s) : B*(a:A)=(a:A)*B := by
    have hBp : Commute p B := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hpM B hB).1.symm
    let b : Corner p hp := ⟨p*B*p,by
      constructor
      · rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq]
      · rw [mul_assoc _ p,hp.isIdempotentElem.eq]⟩
    have hb : b∈StarSubalgebra.centralizer ℂ
        (subalgebraCorner (StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ s : Set A)) p hp hpM : Set (Corner p hp)) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      intro x hx
      have hh := (StarSubalgebra.mem_centralizer_iff ℂ).mp hx B hB
      constructor
      · apply Subtype.ext
        change (x:A)*(p*B*p)=(p*B*p)*(x:A)
        rw [corner_mul_compress p hp B hBp,compress_mul_corner p hp B hBp]
        exact hh.1.symm
      · apply Subtype.ext
        change ((star x : Corner p hp):A)*(p*B*p)=(p*B*p)*((star x : Corner p hp):A)
        rw [corner_mul_compress p hp B hBp,compress_mul_corner p hp B hBp]
        exact ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hx) B hB).1.symm
    have hh := congrArg (fun z : Corner p hp => (z:A))
      (((StarSubalgebra.mem_centralizer_iff ℂ).mp ha b hb).1)
    change (p*B*p)*(a:A)=(a:A)*(p*B*p) at hh
    rwa [compress_mul_corner p hp B hBp,corner_mul_compress p hp B hBp] at hh
  intro B hB
  exact ⟨htest B hB,htest (star B) (star_mem hB)⟩
end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.FreeFock

section
open scoped ENNReal
variable {α : Type u_2} [DecidableEq α]

end

section
variable {α : Type u_3} [DecidableEq α]

end
variable {α : Type u_4} [DecidableEq α]

end FreeGroupFactorMain.FreeFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5

namespace FreeGroupFactorMain.FreeFock

section
open scoped ENNReal
variable {α : Type u_1} [DecidableEq α]

end
section
open scoped ENNReal ComplexConjugate
variable {α : Type u_2} [DecidableEq α]

end
open GaussianRecognition CyclicSpectral CircularRotation
open Filter Topology
open scoped ENNReal
variable {α : Type u_5} [DecidableEq α]

end FreeGroupFactorMain.FreeFock

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem pRep_add (a b : PCorner ℕ) : pRepresentation (a+b)=pRepresentation a+pRepresentation b :=
  (pRepresentation (ι := ℕ)).map_add' a b

theorem pRep_star (a : PCorner ℕ) : pRepresentation (star a)=star (pRepresentation a) :=
  (pRepresentation (ι := ℕ)).map_star' a

theorem pFilled_le_pAmbient : Base u v ≤ pAmbient u v :=
  fun _ ha => filledEdgeAlgebra_le_ambient u v (0:ℕ) 1 ha

theorem kindPair_mem_pAmbient (k : Kind) :
    kindCreator u v k+star (kindCreator u v k.transpose)∈pAmbient u v := by
  cases k with
  | fresh n r s => exact normalizedCreation_paired_mem u v (0:ℕ) (n+2) r s
  | residual r s => exact normalizedResidual_paired_mem u v (0:ℕ) 1 r s
  | diagonal r =>
    change pDiagonal u v 0 0 r+star (pDiagonal u v 0 0 r)∈pAmbient u v
    rw [pDiagonal_eq_pFresh]
    exact normalizedCreation_paired_mem u v (0:ℕ) 0 r r

theorem outputPair_mem_pAmbient (i : WeightedCornerIndex.Index) (n : ℕ) :
    (cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈pAmbient u v := by
  apply ((cornerAbsorption u v hv hvu).output_generation (pAmbient u v)
    (fun i => pFilled_le_pAmbient u v (kindLeft u v (description i)).property)
    (fun i => pFilled_le_pAmbient u v (kindRight u v (description i)).property)).mp ?_ i n
  constructor
  · intro i
    change kindCreator u v (description i)+star (kindCreator u v (description (CircularRotation.flip i)))∈pAmbient u v
    rw [description_flip]
    exact kindPair_mem_pAmbient u v (description i)
  · intro i n
    exact normalizedCreation_paired_mem u v (0:ℕ) (reservoirCode (i,n)+2) false false

theorem representedAmbient_saturated :
    Bicommutant.algebra (representedAmbient u v : Set (PRange ℕ →L[ℂ] PRange ℕ))≤representedAmbient u v := by
  intro T hT
  have him : (representedAmbient u v : Set (PRange ℕ →L[ℂ] PRange ℕ))=
      pRepresentation '' (pAmbient (ι := ℕ) u v : Set (PCorner ℕ)) := by
    ext B
    constructor
    · intro h;exact ⟨(pRepresentation (ι := ℕ)).symm B,h,StarAlgEquiv.apply_symm_apply _ _⟩
    · rintro ⟨b,hb,rfl⟩
      change (pRepresentation (ι := ℕ)).symm (pRepresentation b)∈pAmbient u v
      rw [StarAlgEquiv.symm_apply_apply]
      exact hb
  change (pRepresentation (ι := ℕ)).symm T∈pAmbient u v
  apply relative_corner_bicommutant (insert P (Set.range (S u v : ℕ → Operator ℕ)))
    P projection_P (P_mem_ambient u v)
  apply (bicommutant_transport (A := PCorner ℕ) (B := PRange ℕ →L[ℂ] PRange ℕ) (pRepresentation (ι := ℕ)) (pAmbient (ι := ℕ) u v : Set (PCorner ℕ))
    ((pRepresentation (ι := ℕ)).symm T)).mp
  rw [StarAlgEquiv.apply_symm_apply,← him]
  exact hT

theorem weighted_generated_le_ambient : (weightedSystem u v hv hvu).generated scalarFlip≤representedAmbient u v := by
  apply le_trans (Bicommutant.mono _ (representedAmbient u v : Set (PRange ℕ →L[ℂ] PRange ℕ)) ?_)
    (representedAmbient_saturated u v)
  rintro T (⟨a,rfl⟩|⟨i,rfl⟩)
  · exact pFilled_le_pAmbient u v (weightedUniform_mem u v hv hvu a)
  · change (pRepresentation (ι := ℕ)).symm
      (pRepresentation ((cornerAbsorption u v hv hvu).output i.1 i.2)+
        star (pRepresentation ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i.1) i.2)))∈pAmbient u v
    rw [← pRep_star,← pRep_add,StarAlgEquiv.symm_apply_apply]
    exact outputPair_mem_pAmbient u v hv hvu i.1 i.2

theorem weighted_generated_eq_ambient :
    (weightedSystem u v hv hvu).generated scalarFlip=representedAmbient u v :=
  le_antisymm (weighted_generated_le_ambient u v hv hvu) (representedAmbient_le_weightedGenerated u v hv hvu)
end FreeGroupFactorMain.WeightedFock

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.WeightedFock.weighted_generated_eq_ambient := @OAI.FreeGroupFactorMain.WeightedFock.weighted_generated_eq_ambient
