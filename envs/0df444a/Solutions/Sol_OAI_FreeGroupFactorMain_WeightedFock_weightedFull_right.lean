-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.WeightedFock.weightedFull_right
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:38:24.321352+00:00
-- url     : https://prove2.me/submissions/069b1f18-8206-4781-9af0-e5ac0cb11b65

import Mathlib
import Definitions.Def_FreeGroupFactorProof18
import Theorems.Thm_OAI_FreeGroupFactorMain_WeightedFock_representedAmbient_le_weightedGenerated

set_option linter.all false

section
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12
universe u_13 u_14 u_15

noncomputable section
namespace FreeGroupFactorMain.FreeFock
open scoped ENNReal

variable {α : Type u_2} {β : Type u_3} [DecidableEq α] [DecidableEq β]

end FreeGroupFactorMain.FreeFock
namespace FreeGroupFactorMain.CoordinateProjection

variable {α : Type u_6} [DecidableEq α]
open scoped Classical

end FreeGroupFactorMain.CoordinateProjection

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_11} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_12}

variable [DecidableEq ι]

 theorem P_commute_rightP : Commute (P : Operator ι) rightP := CoordinateProjection.commute _ _

end

section
open FreeFock
variable {ι : Type u_13} [DecidableEq ι]

end

section
open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_14} [DecidableEq ι]

end

open FreeFock
open scoped ComplexConjugate
variable {ι : Type u_15} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

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

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification WeightedCornerIndex

end FreeGroupFactorMain.WeightedFock

namespace FreeGroupFactorMain.Amplification
variable {A : Type u_1} [CStarAlgebra A]

variable {E : Type u_2} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (p : E →L[ℂ] E) (hp : IsStarProjection p) [CompleteSpace p.range]

end FreeGroupFactorMain.Amplification

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification Filter Topology
open scoped ENNReal
variable {ι : Type u_3} [DecidableEq ι]

theorem pProject_coe (ξ : PRange ι) : pProject (ξ:H ι)=ξ :=
  Submodule.orthogonalProjectionOnto_mem_subspace_eq_self ξ

theorem pRange_total (K : Submodule ℂ (PRange ι)) (hK : IsClosed (K : Set (PRange ι)))
    (hb : ∀ w : Path ι, pProject (lp.single 2 w 1)∈K) : K=⊤ := by
  apply top_unique
  intro ξ _
  have hs := (lp.hasSum_single (by norm_num : (2:ℝ≥0∞)≠⊤) (ξ:H ι)).map pProject pProject.continuous
  rw [pProject_coe] at hs
  apply hK.mem_of_tendsto hs
  filter_upwards [] with s
  apply K.sum_mem
  intro w _
  have he : lp.single (E := fun _ : Path ι => ℂ) 2 w ((ξ:H ι) w)=
      ((ξ:H ι) w) • lp.single 2 w 1 := by
    ext q
    simp [lp.single_apply,Pi.single_apply]
  change pProject (lp.single 2 w ((ξ:H ι) w))∈K
  rw [he,map_smul]
  exact K.smul_mem _ (hb w)

end

open FreeFock Amplification
variable {ι : Type u_5} [DecidableEq ι]

theorem pSandwich_commute (B : Operator ι) (hBP : Commute P B)
    (x : PCorner ι) (hBx : Commute (x:Operator ι) B) : Commute (pSandwich B) x := by
  apply Subtype.ext
  change P*B*P*(x:Operator ι)=(x:Operator ι)*(P*B*P)
  calc
    _ = P*(B*(x:Operator ι)) := by rw [mul_assoc (P*B),x.property.1,mul_assoc]
    _ = P*((x:Operator ι)*B) := by rw [hBx.eq]
    _ = (x:Operator ι)*B := by rw [← mul_assoc,x.property.1]
    _ = (x:Operator ι)*(P*B*P) := by
      symm
      rw [← mul_assoc,← mul_assoc,x.property.2,mul_assoc,← hBP.eq,← mul_assoc,x.property.2]

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

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

namespace FreeGroupFactorMain.GaussianRecognition.System
variable {A : Type u_1} {E : Type u_2} {I : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

theorem normal_mem_of_generator_invariant (σ : I → I) (K : Submodule ℂ E)
    (hroot : X.root∈K) (hcoeff : ∀ a ξ,ξ∈K → X.coeff a ξ∈K)
    (hgen : ∀ i ξ,ξ∈K → X.generator σ i ξ∈K) (a : A) (w : List (I×A)) : X.normal a w∈K := by
  have main : ∀ n : ℕ,∀ w : List (I×A),w.length=n → ∀ a : A,X.normal a w∈K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn a
      cases w with
      | nil => simpa only [normal] using hcoeff a X.root hroot
      | cons q w =>
        rcases q with ⟨i,b⟩
        subst n
        have ht := ih w.length (by simp) w rfl b
        have ha : star (X.create (σ i)) (X.normal b w)∈K := by
          cases w with
          | nil => rw [X.annihilate_normal_nil];exact K.zero_mem
          | cons q w =>
            rcases q with ⟨j,c⟩
            rw [X.annihilate_normal_cons]
            exact ih w.length (by simp) w rfl _
        have hh := K.sub_mem (hgen i (X.normal b w) ht) ha
        have he : X.generator σ i (X.normal b w)-star (X.create (σ i)) (X.normal b w)=
            X.create i (X.normal b w) := by simp only [generator,add_apply,add_sub_cancel_right]
        rw [he] at hh
        exact hcoeff a _ hh
  exact main w.length w rfl a

theorem normalHull_le_of_generator_invariant (σ : I → I) (K : Submodule ℂ E)
    (hK : IsClosed (K : Set E)) (hroot : X.root∈K)
    (hcoeff : ∀ a ξ,ξ∈K → X.coeff a ξ∈K)
    (hgen : ∀ i ξ,ξ∈K → X.generator σ i ξ∈K) : X.normalHull≤K := by
  apply Submodule.topologicalClosure_minimal _ ?_ hK
  apply Submodule.span_le.mpr
  rintro ξ ⟨⟨a,w⟩,rfl⟩
  exact X.normal_mem_of_generator_invariant σ K hroot hcoeff hgen a w
end FreeGroupFactorMain.GaussianRecognition.System

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification GaussianRecognition
variable {ι : Type u_4} [DecidableEq ι]

theorem P_range_apply (ξ : PRange ι) : P (ξ:H ι)=(ξ:H ι) := by
  obtain ⟨η,hη⟩ := ξ.property
  rw [← hη]
  exact DFunLike.congr_fun (projection_P (ι := ι)).isIdempotentElem.eq η

def pRight : PRange ι →L[ℂ] PRange ι := pRepresentation (pSandwich rightP)

theorem pRight_apply (ξ : PRange ι) : (pRight ξ : H ι)=rightP (ξ:H ι) := by
  rw [pRight,pRepresentation_apply]
  change P (rightP (P (ξ:H ι)))=rightP (ξ:H ι)
  rw [P_range_apply]
  have h := DFunLike.congr_fun (P_commute_rightP (ι := ι)).eq (ξ:H ι)
  change P (rightP (ξ:H ι))=rightP (P (ξ:H ι)) at h
  rwa [P_range_apply] at h

theorem pRight_projection : IsStarProjection (pRight : PRange ι →L[ℂ] PRange ι) := by
  constructor
  · apply ContinuousLinearMap.ext
    intro ξ
    apply Subtype.ext
    change (pRight (pRight ξ) : H ι)=(pRight ξ : H ι)
    simp only [pRight_apply]
    exact DFunLike.congr_fun (rightP_projection (ι := ι)).isIdempotentElem.eq (ξ:H ι)
  · have hs : star (pSandwich (rightP : Operator ι))=pSandwich rightP := by
      apply Subtype.ext
      change star (P*rightP*P : Operator ι)=P*rightP*P
      simp only [star_mul,projection_P.isSelfAdjoint.star_eq,rightP_projection.isSelfAdjoint.star_eq,mul_assoc]
    exact ((pRepresentation (ι := ι)).map_star' (pSandwich rightP)).symm.trans
      (congrArg (pRepresentation (ι := ι)) hs)

theorem pRight_root : (pRight : PRange ι →L[ℂ] PRange ι) pRoot=pRoot := by
  apply Subtype.ext
  rw [pRight_apply]
  change CoordinateProjection.proj _ (lp.single 2 ([],true) 1)=_
  simp only [CoordinateProjection.proj_single,Set.mem_ofPred_eq,ite_true]
  rfl

theorem pRight_commute_ambient (u v : ℝ) (T : representedAmbient u v) :
    Commute (pRight : PRange ℕ →L[ℂ] PRange ℕ) T.val := by
  let x := (pRepresentation (ι := ℕ)).symm T.val
  have hx : (x:Operator ℕ)∈ambientAlgebra u v := T.property
  have hc : Commute (x:Operator ℕ) rightP :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx rightP (rightP_mem_commutant u v)).1.symm
  have hh : Commute (pRepresentation (pSandwich rightP)) (pRepresentation x) := by
    change _ * _ = _ * _
    simpa only [map_mul] using congrArg (fun X : PCorner ℕ => pRepresentation X)
      (pSandwich_commute rightP P_commute_rightP x hc).eq
  change Commute (pRepresentation (pSandwich rightP)) (pRepresentation ((pRepresentation (ι := ℕ)).symm T.val)) at hh
  rw [StarAlgEquiv.apply_symm_apply] at hh
  exact hh

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem weighted_normalHull_le_right :
    (weightedSystem u v hv hvu).normalHull≤(pRight : PRange ℕ →L[ℂ] PRange ℕ).range := by
  have hpres (T : representedAmbient u v) (ξ : PRange ℕ) (hξ : ξ∈(pRight : PRange ℕ →L[ℂ] PRange ℕ).range) :
      T.val ξ∈(pRight : PRange ℕ →L[ℂ] PRange ℕ).range := by
    obtain ⟨η,rfl⟩ := hξ
    exact ⟨T.val η,(DFunLike.congr_fun (pRight_commute_ambient u v T).eq η)⟩
  apply (weightedSystem u v hv hvu).normalHull_le_of_generator_invariant scalarFlip _
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range pRight_projection.isIdempotentElem)
    ⟨pRoot,pRight_root⟩
  · intro a ξ hξ
    exact hpres ⟨(weightedSystem u v hv hvu).coeff a,
      weighted_generated_le_ambient u v hv hvu (Bicommutant.subset _ (Or.inl (Set.mem_range_self a)))⟩ ξ hξ
  · intro i ξ hξ
    exact hpres ⟨(weightedSystem u v hv hvu).generator scalarFlip i,
      weighted_generated_le_ambient u v hv hvu (Bicommutant.subset _ (Or.inr (Set.mem_range_self i)))⟩ ξ hξ

theorem pRight_pSandwich_basis (w : Path ι) (B : Operator ι) (hB : B (vacuum u v)=lp.single 2 w 1)
    (hBc : Commute B rightP) :
    (u:ℂ) • pRepresentation (pSandwich B) pRoot=pRight (pProject (lp.single 2 w 1)) := by
  apply Subtype.ext
  change (u:ℂ) • (pRepresentation (pSandwich B) pRoot : H ι)=_
  rw [pRepresentation_apply,pRight_apply,pProject_val,← hB]
  change (u:ℂ) • ((P*B*P : Operator ι) (lp.single 2 ([],true) 1))=rightP (P (B (vacuum u v)))
  have he : (u:ℂ) • lp.single 2 ([],true) 1=rightP (vacuum u v : H ι) := by
    simp only [vacuum,map_add,map_smul,rightP,CoordinateProjection.proj_single,Set.mem_ofPred_eq,
      ite_true,Bool.false_eq_true,ite_false,smul_zero,add_zero]
  rw [← map_smul,he]
  have hpv : P (rightP (vacuum u v : H ι))=rightP (vacuum u v : H ι) := by
    rw [← he,map_smul,P_nil_true]
  change P (B (P (rightP (vacuum u v))))=rightP (P (B (vacuum u v)))
  have hb : B (rightP (vacuum u v))=rightP (B (vacuum u v)) := DFunLike.congr_fun hBc.eq _
  rw [hpv,hb]
  exact DFunLike.congr_fun (P_commute_rightP (ι := ι)).eq (B (vacuum u v))
theorem right_le_weighted_normalHull :
    (pRight : PRange ℕ →L[ℂ] PRange ℕ).range≤(weightedSystem u v hv hvu).normalHull := by
  let K := (weightedSystem u v hv hvu).normalHull
  have he : K.comap (pRight : PRange ℕ →L[ℂ] PRange ℕ).toLinearMap=⊤ := by
    apply pRange_total _
      ((Submodule.isClosed_topologicalClosure _).preimage pRight.continuous)
    intro w
    obtain ⟨B,hB,hh⟩ := good_basis u v (hv.trans hvu).ne' hv.ne' w
    have hBc : Commute B rightP :=
      ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB.1 rightP (rightP_mem_commutant u v)).1.symm
    change pRight (pProject (lp.single 2 w 1))∈K
    rw [← pRight_pSandwich_basis u v w B hh hBc]
    apply K.smul_mem
    apply (weightedSystem u v hv hvu).normalHull_bicommutant scalarFlip
    apply representedAmbient_le_weightedGenerated u v hv hvu
    change (pRepresentation (ι := ℕ)).symm (pRepresentation (pSandwich B))∈pAmbient u v
    rw [StarAlgEquiv.symm_apply_apply]
    exact mul_mem (mul_mem (P_mem_ambient u v) hB.1) (P_mem_ambient u v)
  rintro ξ ⟨η,rfl⟩
  have hh : η∈K.comap (pRight : PRange ℕ →L[ℂ] PRange ℕ).toLinearMap := by rw [he];trivial
  exact hh

theorem weighted_normalHull_eq_right :
    (weightedSystem u v hv hvu).normalHull=(pRight : PRange ℕ →L[ℂ] PRange ℕ).range :=
  le_antisymm (weighted_normalHull_le_right u v hv hvu) (right_le_weighted_normalHull u v hv hvu)
end

open FreeFock Amplification GaussianRecognition
variable {ι : Type u_5} [DecidableEq ι]

theorem reverseConj_square (T : Operator ι) : reverseConj (reverseConj T)=T := by
  apply ContinuousLinearMap.ext
  intro ξ
  simp only [reverseConj_apply,reverseOperator_involutive]

theorem reverseConj_mem_commutant (u v : ℝ) (T : Operator ι) (hT : T∈ambientAlgebra u v) :
    reverseConj T∈ambientCommutant u v := by
  have htest (y : Operator ι) (hy : y∈insert P (Set.range (S u v : ι → Operator ι))) : Commute y (reverseConj T) := by
    have hyr : reverseConj y∈ambientCommutant u v := by
      rcases hy with rfl | ⟨i,rfl⟩
      · rw [reverseConj_P];exact rightP_mem_commutant u v
      · rw [reverseConj_S];exact rightS_mem_commutant u v i
    have hc : Commute (reverseConj y) T := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hT _ hyr).1
    have hh := Commute.map hc reverseConj.toStarAlgHom
    change Commute (reverseConj (reverseConj y)) (reverseConj T) at hh
    simpa only [reverseConj_square] using hh
  rw [ambientCommutant,StarSubalgebra.mem_centralizer_iff]
  intro y hy
  have hs : star y=y := by
    rcases hy with rfl | ⟨i,rfl⟩
    · exact projection_P.isSelfAdjoint.star_eq
    · exact (S_selfAdjoint u v i).star_eq
  exact ⟨(htest y hy).eq,by rw [hs];exact (htest y hy).eq⟩

theorem pSandwich_rep_apply (B : Operator ι) (hBP : Commute P B) (ξ : PRange ι) :
    (pRepresentation (pSandwich B) ξ : H ι)=B (ξ:H ι) := by
  rw [pRepresentation_apply]
  change P (B (P (ξ:H ι)))=B (ξ:H ι)
  rw [P_range_apply]
  have hh := DFunLike.congr_fun hBP.eq (ξ:H ι)
  change P (B (ξ:H ι))=B (P (ξ:H ι)) at hh
  rwa [P_range_apply] at hh

variable (u v : ℝ)

theorem rightEdge_mem : rightEdge u v∈ambientCommutant u v :=
  reverseConj_mem_commutant u v _ (edgePolar_mem_ambient u v (0:ℕ))

theorem P_commute_rightEdge : Commute P (rightEdge u v) :=
  ((StarSubalgebra.mem_centralizer_iff ℂ).mp (rightEdge_mem u v) P (Set.mem_insert _ _)).1

theorem pRightEdge_apply (ξ : PRange ℕ) : (pRightEdge u v ξ : H ℕ)= rightEdge u v (ξ:H ℕ) :=
  pSandwich_rep_apply _ (P_commute_rightEdge u v) ξ

theorem pRightEdge_right : pRightEdge u v*(1-pRight)=pRightEdge u v := by
  have he := congrArg (reverseConj (ι := ℕ)) (edgePolar_right u v (0:ℕ))
  rw [map_mul,map_sub,map_one,reverseConj_P] at he
  apply ContinuousLinearMap.ext
  intro ξ
  apply Subtype.ext
  change (pRightEdge u v (ξ-pRight ξ) : H ℕ)=(pRightEdge u v ξ:H ℕ)
  rw [pRightEdge_apply,pRightEdge_apply]
  change rightEdge u v ((ξ:H ℕ)-(pRight ξ : H ℕ))=rightEdge u v (ξ:H ℕ)
  rw [pRight_apply]
  exact DFunLike.congr_fun he (ξ:H ℕ)

variable (hv : 0<v) (hvu : v<u)

theorem starProjection_congr {E : Type u_6} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (K L : Submodule ℂ E) [CompleteSpace K] [CompleteSpace L] (he : K=L) : K.starProjection=L.starProjection := by
  subst L
  rfl

theorem weightedHull_projection : (weightedSystem u v hv hvu).normalHull.starProjection=pRight := by
  let : CompleteSpace (pRight : PRange ℕ →L[ℂ] PRange ℕ).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range pRight_projection.isIdempotentElem).completeSpace_coe
  exact (starProjection_congr _ _ (weighted_normalHull_eq_right u v hv hvu)).trans
    (Amplification.projectionRange_starProjection _ pRight_projection)

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

section
namespace FreeGroupFactorMain.FullReducingCorner
open Amplification GaussianRecognition
variable {A : Type u_1} {B : Type u_2} [CStarAlgebra A] [CStarAlgebra B]

variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable (K : Submodule ℂ E) [CompleteSpace K]

variable (s : Set (E →L[ℂ] E))
variable (hps : K.starProjection∈StarSubalgebra.centralizer ℂ s)
variable (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ s)
variable (hpv : K.starProjection*v=v) (hvr : v*(1-K.starProjection)=v) (hvi : star v*v=1-K.starProjection)

end FreeGroupFactorMain.FullReducingCorner

namespace FreeGroupFactorMain.GaussianRecognition.System
open  FullReducingCorner
variable {A : Type u_5} {E : Type u_6} {I : Type u_7} [Ring A] [StarRing A] [Algebra ℂ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {covariance : I → I → A → A} (X : System A E I covariance)

variable (σ : I → I) (v : E →L[ℂ] E) (hvs : v∈StarSubalgebra.centralizer ℂ (X.generators σ))
variable (hpv : X.normalHull.starProjection*v=v) (hvr : v*(1-X.normalHull.starProjection)=v)
variable (hvi : star v*v=1-X.normalHull.starProjection)

end FreeGroupFactorMain.GaussianRecognition.System

end

namespace FreeGroupFactorMain.WeightedFock
open FreeFock Amplification GaussianRecognition
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem weightedFull_right :
    pRightEdge u v*(1-(weightedSystem u v hv hvu).normalHull.starProjection)=pRightEdge u v := by
  rw [weightedHull_projection]
  exact pRightEdge_right u v

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.WeightedFock.weightedFull_right := @OAI.FreeGroupFactorMain.WeightedFock.weightedFull_right
