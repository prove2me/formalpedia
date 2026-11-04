-- Prove2me | solution 1 for OAI.FreeGroupFactorMain.WeightedFock.representedAmbient_le_weightedGenerated
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-11-04T03:49:50.265964+00:00
-- url     : https://prove2.me/submissions/a663da2e-1a34-472e-bed2-d79fc0d44648

import Mathlib
import Definitions.Def_FreeGroupFactorProof18

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

def compressed (u v : ℝ) (i : ι) : Operator ι := P*S u v i*P

theorem compressed_formula (u v : ℝ) (i : ι) :
    compressed u v i=(u:ℂ) • (P*creation i true*P + P*star (creation i true)*P) := by
  have hf : star (creation i false)*(P : Operator ι)=0 := by
    have h := congrArg star (P_creation_false i)
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,star_zero (Operator ι)] using h
  simp only [compressed,S,mul_add,add_mul,star_add (R := Operator ι),star_smul,Complex.star_def,
    Complex.conj_ofReal,mul_smul_comm,smul_mul_assoc,mul_assoc,P_creation_false,hf,
    mul_zero,zero_mul,smul_zero,add_zero,smul_add]

end

section
open FreeFock
variable {ι : Type u_11} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_12}

variable [DecidableEq ι]

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

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.Amplification.Polar

section

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
section
variable {E : Type u_3} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
section
variable {E : Type u_4} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end
variable {E : Type u_5} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
open Amplification.Polar
variable {ι : Type u_6} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Amplification.Polar
variable {E : Type u_7} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.Amplification.Polar
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock
open Amplification.Polar
variable {ι : Type u_8} [DecidableEq ι]

 theorem edgeRange_mem_ambient (u v : ℝ) (i : ι) : edgeRange u v i ∈ ambientAlgebra u v :=
  mul_mem (edgePolar_mem_ambient u v i) (star_mem (edgePolar_mem_ambient u v i))

end
open FreeFock
open scoped ENNReal
open Amplification.Polar
variable {ι : Type u_9} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9

namespace FreeGroupFactorMain.CornerRerouting

section
variable {A : Type u_1} [Ring A] [StarRing A]

 def Supported (p x : A) : Prop := p*x=x ∧ x*p=x
 def lift (v t : A) : A := t+star v*t*v

 theorem supported_star {p t : A} (hp : IsSelfAdjoint p) (ht : Supported p t) :
    Supported p (star t) := by
  constructor
  · simpa only [star_mul,hp.star_eq] using congrArg star ht.2
  · simpa only [star_mul,hp.star_eq] using congrArg star ht.1

 theorem supported_mul_star_zero {p v t : A} (hvp : v*p=0) (hp : IsSelfAdjoint p)
    (ht : Supported p t) : t*star v=0 := by
  calc
    _ = (t*p)*star v := by rw [ht.2]
    _ = t*(p*star v) := mul_assoc _ _ _
    _ = 0 := by rw [star_left_zero hp hvp,mul_zero]

omit [StarRing A] in
 theorem mul_supported_zero {p v t : A} (hvp : v*p=0) (ht : Supported p t) : v*t=0 := by
  calc
    _ = v*(p*t) := by rw [ht.1]
    _ = (v*p)*t := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hvp,zero_mul]

 theorem lift_mul_supported {p v t y : A} (hvp : v*p=0) (hy : Supported p y) :
    lift v t*y=t*y := by
  unfold lift
  rw [add_mul,mul_assoc (star v*t),mul_supported_zero hvp hy,mul_zero,add_zero]

 theorem supported_mul_lift {p v t y : A} (hp : IsSelfAdjoint p) (hvp : v*p=0)
    (hy : Supported p y) : y*lift v t=y*t := by
  unfold lift
  rw [mul_add,← mul_assoc y,← mul_assoc y,supported_mul_star_zero hvp hp hy,
    zero_mul,zero_mul,add_zero]

 theorem lift_commute_supported {p v t y : A} (hp : IsSelfAdjoint p) (hvp : v*p=0)
    (hy : Supported p y) (h : Commute t y) : Commute (lift v t) y := by
  change lift v t*y=y*lift v t
  rw [lift_mul_supported hvp hy,supported_mul_lift hp hvp hy]
  exact h.eq

omit [StarRing A] in
 theorem square_zero {p v : A} (hpv : p*v=v) (hvp : v*p=0) : v*v=0 := by
  calc
    _ = v*(p*v) := by rw [hpv]
    _ = (v*p)*v := (mul_assoc _ _ _).symm
    _ = 0 := by rw [hvp,zero_mul]

 theorem range_mul {p v : A} (hi : star v*v=1-p) (hr : v*(1-p)=v) :
    (v*star v)*v=v := by rw [mul_assoc,hi,hr]

 theorem lift_commute_edge {p v t : A} (hpv : p*v=v) (hvp : v*p=0)
    (hi : star v*v=1-p) (hr : v*(1-p)=v) (ht : Supported p t)
    (htr : Commute t (v*star v)) : Commute (lift v t) v := by
  change lift v t*v=v*lift v t
  have hleft : lift v t*v=t*v := by
    unfold lift
    rw [add_mul,mul_assoc (star v*t),square_zero hpv hvp,mul_zero,add_zero]
  have hright : v*lift v t=t*v := by
    unfold lift
    rw [mul_add,mul_supported_zero hvp ht,zero_add,← mul_assoc v,← mul_assoc v,
      ← htr.eq,mul_assoc t,range_mul hi hr]
  exact hleft.trans hright.symm

 theorem star_lift (v t : A) : star (lift v t)=lift v (star t) := by
  simp only [lift,star_add,star_mul,star_star,mul_assoc]

 theorem lift_commute_edge_star {p v t : A} (hp : IsSelfAdjoint p)
    (hpv : p*v=v) (hvp : v*p=0) (hi : star v*v=1-p) (hr : v*(1-p)=v)
    (ht : Supported p t) (htr : Commute t (v*star v)) :
    Commute (lift v t) (star v) := by
  have hs : Commute (star t) (v*star v) := by
    simpa only [star_mul,star_star] using htr.star_star
  have hh := (lift_commute_edge hpv hvp hi hr (supported_star hp ht) hs).star_star
  simpa only [star_lift,star_star] using hh

 def diagonal (p s : A) : A := p*s*p
 def offDiagonal (p v s : A) : A := p*s*(1-p)*star v
 def remaining (p v s : A) : A := v*(1-p)*s*(1-p)*star v

omit [StarRing A] in
 theorem diagonal_supported {p s : A} (hp : IsIdempotentElem p) : Supported p (diagonal p s) := by
  constructor
  · simp only [diagonal,← mul_assoc,hp.eq]
  · simp only [diagonal,mul_assoc,hp.eq]

 theorem offDiagonal_supported {p v s : A} (hp : IsStarProjection p) (hpv : p*v=v) :
    Supported p (offDiagonal p v s) := by
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  constructor
  · simp only [offDiagonal,← mul_assoc,hp.isIdempotentElem.eq]
  · simp only [offDiagonal,mul_assoc,hvsp]

 theorem remaining_supported {p v s : A} (hp : IsSelfAdjoint p) (hpv : p*v=v) :
    Supported p (remaining p v s) := by
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.star_eq] using congrArg star hpv
  constructor
  · simp only [remaining,← mul_assoc,hpv]
  · simp only [remaining,mul_assoc,hvsp]

 theorem reconstruct {p v s : A} (hp : IsStarProjection p) (hi : star v*v=1-p)
    (hs : IsSelfAdjoint s) :
    s=diagonal p s + offDiagonal p v s*v + star v*star (offDiagonal p v s) +
      star v*remaining p v s*v := by
  have hq : (1-p)*(1-p)=1-p := hp.one_sub.isIdempotentElem.eq
  have h₁ : offDiagonal p v s*v=p*s*(1-p) := by
    simp only [offDiagonal,mul_assoc,hi]
    rw [hq]
  have h₂ : star v*star (offDiagonal p v s)=(1-p)*s*p := by
    unfold offDiagonal
    rw [star_mul,star_mul,star_mul,star_star,star_sub,star_one,
      hp.isSelfAdjoint.star_eq,hs.star_eq]
    simp only [← mul_assoc,hi,hq]
  have h₃ : star v*remaining p v s*v=(1-p)*s*(1-p) := by
    simp only [remaining,← mul_assoc,hi,hq]
    simp only [mul_assoc,hi]
    rw [← mul_assoc (1-p),hq,mul_assoc]
  rw [h₁,h₂,h₃,diagonal]
  noncomm_ring

 theorem lift_commute_generator {p v t s : A} (hp : IsStarProjection p)
    (hpv : p*v=v) (hr : v*(1-p)=v) (hi : star v*v=1-p)
    (ht : Supported p t) (hs : IsSelfAdjoint s)
    (htr : Commute t (v*star v)) (ha : Commute t (diagonal p s))
    (hb : Commute t (offDiagonal p v s)) (hbs : Commute t (star (offDiagonal p v s)))
    (hc : Commute t (remaining p v s)) : Commute (lift v t) s := by
  have hvp := right_zero hr
  have ha' := lift_commute_supported hp.isSelfAdjoint hvp (diagonal_supported hp.isIdempotentElem) ha
  have hb' := lift_commute_supported hp.isSelfAdjoint hvp (offDiagonal_supported hp hpv) hb
  have hbs' := lift_commute_supported hp.isSelfAdjoint hvp
    (supported_star hp.isSelfAdjoint (offDiagonal_supported hp hpv)) hbs
  have hc' := lift_commute_supported hp.isSelfAdjoint hvp (remaining_supported hp.isSelfAdjoint hpv) hc
  have hv' := lift_commute_edge hpv hvp hi hr ht htr
  have hvs' := lift_commute_edge_star hp.isSelfAdjoint hpv hvp hi hr ht htr
  rw [reconstruct hp hi hs]
  exact ((ha'.add_right (hb'.mul_right hv')).add_right (hvs'.mul_right hbs')).add_right
    ((hvs'.mul_right hc').mul_right hv')

end
section
variable {A : Type u_2} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]
variable {ι : Type u_3}

 theorem corner_bicommutant {p v x t : A} {s : ι → A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hr : v*(1-p)=v) (hi : star v*v=1-p)
    (hx : x ∈ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (insert p (Set.range s)) : Set A))
    (hxs : Supported p x) (ht : Supported p t) (hs : ∀ i, IsSelfAdjoint (s i))
    (htr : Commute t (v*star v)) (ha : ∀ i, Commute t (diagonal p (s i)))
    (hb : ∀ i, Commute t (offDiagonal p v (s i)))
    (hbs : ∀ i, Commute t (star (offDiagonal p v (s i))))
    (hc : ∀ i, Commute t (remaining p v (s i))) : Commute t x := by
  have hvp := right_zero hr
  have htp : Commute t p := ht.2.trans ht.1.symm
  have hpp : Supported p p := ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
  have hLP := lift_commute_supported hp.isSelfAdjoint hvp hpp htp
  have hLS (i : ι) : Commute (lift v t) (s i) :=
    lift_commute_generator hp hpv hr hi ht (hs i) htr (ha i) (hb i) (hbs i) (hc i)
  have hL : lift v t ∈ StarSubalgebra.centralizer ℂ (insert p (Set.range s)) := by
    rw [StarSubalgebra.mem_centralizer_iff]
    intro y hy
    rcases Set.mem_insert_iff.mp hy with rfl | ⟨i,rfl⟩
    · exact ⟨hLP.symm,by simpa only [hp.isSelfAdjoint.star_eq] using hLP.symm.eq⟩
    · exact ⟨(hLS i).symm,by simpa only [(hs i).star_eq] using (hLS i).symm.eq⟩
  have he := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hx (lift v t) hL).1
  change t*x=x*t
  simpa only [lift_mul_supported hvp hxs,supported_mul_lift hp.isSelfAdjoint hvp hxs] using he

end
variable {A : Type u_4} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification.Polar
variable {ι : Type u_5} [DecidableEq ι]

end
section
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_7} [DecidableEq ι]

end

section
open FreeFock
variable {ι : Type u_8} [DecidableEq ι]

end
open FreeFock
variable {ι : Type u_9} [DecidableEq ι]

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

section
namespace OAI

noncomputable section

universe u_1 u_2 u_3 u_4 u_5 u_6

open Filter Topology
namespace FreeGroupFactorMain.OrthogonalSpectralSum
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

end FreeGroupFactorMain.OrthogonalSpectralSum
namespace FreeGroupFactorMain.SpectralSeparation
variable {A : Type u_2} [NormedRing A] [NormedAlgebra ℂ A] [StarRing A] [StarModule ℂ A]

end FreeGroupFactorMain.SpectralSeparation
namespace FreeGroupFactorMain.CornerRerouting
variable {A : Type u_3} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.CornerRerouting
namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_4} [DecidableEq ι]

theorem range_mul_defectSemicircle (u v : ℝ) (i j : ι) :
    edgeRange u v i*defectSemicircle u v i j=0 := by
  rw [← defectSemicircle_left u v i j,← mul_assoc,edgeRange_mul_defect,zero_mul]

theorem defectSemicircle_mul_range (u v : ℝ) (i j : ι) :
    defectSemicircle u v i j*edgeRange u v i=0 := by
  simpa only [star_mul,(edgeRange_projection u v i).isSelfAdjoint.star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq,star_zero (Operator ι)]
    using congrArg star (range_mul_defectSemicircle u v i j)

theorem defectSemicircle_mul_P (u v : ℝ) (i j : ι) :
    defectSemicircle u v i j*P=defectSemicircle u v i j := by
  simpa only [star_mul,projection_P.isSelfAdjoint.star_eq,
    (defectSemicircle_selfAdjoint u v i j).star_eq] using congrArg star (P_mul_defectSemicircle u v i j)

theorem compressed_edge_formula (u v : ℝ) (i : ι) :
    compressed u v i=(u:ℂ) • (edgeCreation i true true+star (edgeCreation i true true)) := by
  rw [compressed_formula]
  simp only [edgeCreation,vertex,ite_true,star_mul,projection_P.isSelfAdjoint.star_eq,P_creation_true]
  have hs : star (creation i true)*P=star (creation i true) := by
    simpa only [star_mul,projection_P.isSelfAdjoint.star_eq] using congrArg star (P_creation_true i)
  rw [mul_assoc,hs]

theorem defectSemicircle_smul (u v : ℝ) (i j : ι) :
    (u:ℂ) • defectSemicircle u v i j=edgeDefect u v i*S u v j*edgeDefect u v i := by
  have he : edgeDefect u v i*compressed u v j*edgeDefect u v i=
      edgeDefect u v i*S u v j*edgeDefect u v i := by
    rw [compressed,← mul_assoc,← mul_assoc,edgeDefect_mul_P,mul_assoc (edgeDefect u v i*S u v j),P_mul_edgeDefect]
  rw [← he,compressed_edge_formula,mul_smul_comm,smul_mul_assoc]
  congr 1
  simp only [defectSemicircle,defectCreation,star_mul,
    (edgeDefect_projection u v i).isSelfAdjoint.star_eq,mul_add,add_mul,mul_assoc]

theorem defectSemicircle_mem_ambient (u v : ℝ) (hu : u≠0) (i j : ι) :
    defectSemicircle u v i j∈ambientAlgebra u v := by
  have hd : edgeDefect u v i∈ambientAlgebra u v :=
    sub_mem (P_mem_ambient u v) (edgeRange_mem_ambient u v i)
  have hm : (u:ℂ) • defectSemicircle u v i j∈ambientAlgebra u v := by
    rw [defectSemicircle_smul]
    exact mul_mem (mul_mem hd (S_mem_ambient u v j)) hd
  have hh := (ambientAlgebra u v).smul_mem hm (u:ℂ)⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul] using hh

theorem oldBaseGenerator_mem_ambient (u v : ℝ) (hu : u≠0) (i j : ι) :
    oldBaseGenerator u v i j∈ambientAlgebra u v :=
  add_mem (add_mem (mul_mem (offDiagonal_mem_ambient u v i) (star_mem (edgePolar_mem_ambient u v i)))
    (defectSemicircle_mem_ambient u v hu i j))
    ((ambientAlgebra u v).smul_mem (edgeRange_mem_ambient u v i) _)

end FreeGroupFactorMain.WeightedFock
namespace FreeGroupFactorMain.Bicommutant
variable {A : Type u_5} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

end FreeGroupFactorMain.Bicommutant

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_6} [DecidableEq ι]

theorem P_mem_diffuseBase (u v : ℝ) (i j : ι) : P∈diffuseBase u v i j :=
  Bicommutant.subset _ (Set.mem_insert _ _)

theorem edgeRange_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    edgeRange u v i∈diffuseBase u v i j := by
  have hrf : Commute (edgeRange u v i) (leftModulus u v i+defectSemicircle u v i j) := by
    change _*(_+_)=(_+_)*_
    rw [mul_add,add_mul,range_mul_leftModulus u v hv.le hvu,leftModulus_mul_range u v hv.le hvu,
      range_mul_defectSemicircle,defectSemicircle_mul_range]
  have hh := SpectralSeparation.separated_projection_mem (edgeRange_projection u v i)
    ((leftModulus_selfAdjoint u v i).add (defectSemicircle_selfAdjoint u v i j)) hrf
    (oldBaseShift u v i j) (by dsimp [oldBaseShift]; linarith)
  exact Bicommutant.mono {oldBaseGenerator u v i j} (insert P {oldBaseGenerator u v i j})
    (Set.subset_insert _ _) hh

theorem leftModulus_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    leftModulus u v i∈diffuseBase u v i j := by
  have hr := edgeRange_mem_diffuseBase u v hv hvu i j
  have he : edgeRange u v i*oldBaseGenerator u v i j-
      (oldBaseShift u v i j:ℂ) • edgeRange u v i=leftModulus u v i := by
    rw [oldBaseGenerator,mul_add,mul_add,range_mul_leftModulus u v hv.le hvu,
      range_mul_defectSemicircle,add_zero,mul_smul_comm,(edgeRange_projection u v i).isIdempotentElem.eq,
      add_sub_cancel_right]
  rw [← he]
  exact sub_mem (mul_mem hr (oldBaseGenerator_mem_diffuseBase u v i j))
    ((diffuseBase u v i j).smul_mem hr _)

theorem defectSemicircle_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι) :
    defectSemicircle u v i j∈diffuseBase u v i j := by
  have he : oldBaseGenerator u v i j-leftModulus u v i-
      (oldBaseShift u v i j:ℂ) • edgeRange u v i=defectSemicircle u v i j := by
    rw [oldBaseGenerator]; abel
  rw [← he]
  exact sub_mem (sub_mem (oldBaseGenerator_mem_diffuseBase u v i j)
    (leftModulus_mem_diffuseBase u v hv hvu i j))
    ((diffuseBase u v i j).smul_mem (edgeRange_mem_diffuseBase u v hv hvu i j) _)

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

theorem residualPair_none_none (u v : ℝ) (i j : ι) :
    residualPair u v i j none none=(u:ℂ) • defectSemicircle u v i j := by
  rw [residualPair_eq]
  change edgeDefect u v i*S u v j*star (edgeDefect u v i)=_
  rw [(edgeDefect_projection u v i).isSelfAdjoint.star_eq,defectSemicircle_smul]

theorem residualLeg_sum (u v : ℝ) (i : ι) :
    residualLeg u v i none+residualLeg u v i (some false)=P := by
  change (P-edgeRange u v i)+edgeRange u v i=P
  abel

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
namespace FreeGroupFactorMain.WeightedCornerIndex
open CircularRotation

namespace Kind

end Kind

theorem description_indexOf (k : Kind) (hk : k.valid) : description (indexOf k)=k := by
  cases k with
  | fresh n r s =>
      cases r <;> cases s
      all_goals first | exact False.elim (hk ⟨rfl,rfl⟩) | rfl
  | residual r s =>
      rcases r with _|(_|_) <;> rcases s with _|(_|_)
      all_goals first | exact False.elim (hk ⟨rfl,rfl⟩) | rfl
  | diagonal b => rfl

end FreeGroupFactorMain.WeightedCornerIndex

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

theorem pSandwich_basis (u v : ℝ) (w : Path ι) (B : Operator ι)
    (hBP : Commute P B) (hB : B (vacuum u v)=lp.single 2 w 1) :
    (u:ℂ) • pRepresentation (pSandwich B) pRoot=pProject (lp.single 2 w 1) := by
  apply Subtype.ext
  change (u:ℂ) • (pRepresentation (pSandwich B) pRoot : H ι)=_
  rw [pRepresentation_apply,pProject_val,← hB]
  change (u:ℂ) • ((P*B*P : Operator ι) ((pRoot : PRange ι):H ι))=P (B (vacuum u v))
  rw [← map_smul,← pRoot_vacuum]
  have he : P*B*P*P=P*B := by
    rw [mul_assoc (P*B),projection_P.isIdempotentElem.eq,mul_assoc,← hBP.eq,
      ← mul_assoc,projection_P.isIdempotentElem.eq]
  exact DFunLike.congr_fun he (vacuum u v)

set_option synthInstance.maxHeartbeats 200000 in
theorem oldBaseOp_commutant_total (u v : ℝ) (hu : u≠0) (hv : v≠0) (i j : ι) :
    (Submodule.span ℂ (Set.range (fun B : StarSubalgebra.centralizer ℂ
      (Bicommutant.algebra ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι)) :
        Set (PRange ι →L[ℂ] PRange ι)) => (B:PRange ι →L[ℂ] PRange ι) pRoot))).topologicalClosure=⊤ := by
  let N := StarSubalgebra.centralizer ℂ
    (Bicommutant.algebra ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι)) :
      Set (PRange ι →L[ℂ] PRange ι))
  let K := (Submodule.span ℂ (Set.range (fun B : N => (B:PRange ι →L[ℂ] PRange ι) pRoot))).topologicalClosure
  apply pRange_total K (Submodule.isClosed_topologicalClosure _)
  intro w
  obtain ⟨B,hB,heB,_⟩ := good_right_basis u v hu hv w
  have hBP : Commute P B := ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB P (Set.mem_insert _ _)).1
  have hBA : Commute (oldBaseGenerator u v i j) B :=
    ((StarSubalgebra.mem_centralizer_iff ℂ).mp (oldBaseGenerator_mem_ambient u v hu i j) B hB).1.symm
  have hc : Commute (pRepresentation (pSandwich B)) (pRepresentation (oldBaseCorner u v i j)) := by
    change _ * _ = _ * _
    simpa only [map_mul] using congrArg (fun x : PCorner ι => pRepresentation x)
      (pSandwich_commute B hBP (oldBaseCorner u v i j) hBA).eq
  have hm : pRepresentation (pSandwich B)∈N := by
    apply centralizer_bicommutant ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι))
      ⟨pRepresentation (pSandwich B),?_⟩
    rw [StarSubalgebra.mem_centralizer_iff]
    intro T hT
    rcases hT with rfl
    exact ⟨hc.symm,(by rw [(oldBaseOp_selfAdjoint u v i j).star_eq]; exact hc.symm)⟩
  rw [← pSandwich_basis u v w B hBP heB]
  exact K.smul_mem _ (Submodule.le_topologicalClosure _
    (Submodule.subset_span (Set.mem_range_self (⟨pRepresentation (pSandwich B),hm⟩:N))))
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

theorem filled_edge_corner_generated {p v x d a : A}
    (hp : IsStarProjection p) (hpv : p*v=v) (hvr : v*(1-p)=v)
    (hvi : star v*v=1-p) (hpx : p*x=x) (hxr : x*(1-p)=x)
    (hf : IsSelfAdjoint (x*star v)) (hd : IsSelfAdjoint d) (hds : Supported p d)
    (ha : a∈Bicommutant.algebra (insert d (Bicommutant.algebra (insert p {x+star x}) : Set A)))
    (has : Supported p a) :
    a∈Bicommutant.algebra (insert p (insert (v*star v) (insert (x*star v) {d}))) := by
  have hvp := right_zero hvr
  have hvsp : star v*p=star v := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpv
  have hfs : Supported p (x*star v) :=
    ⟨by rw [← mul_assoc,hpx],by rw [mul_assoc,hvsp]⟩
  have hrs : Supported p (v*star v) :=
    ⟨by rw [← mul_assoc,hpv],by rw [mul_assoc,hvsp]⟩
  have htest (t : A) (ht : t∈StarSubalgebra.centralizer ℂ
      (insert p (insert (v*star v) (insert (x*star v) {d})))) : Commute t a := by
    have hc := (StarSubalgebra.mem_centralizer_iff ℂ).mp ht
    have htp : Commute p t := (hc _ (Set.mem_insert _ _)).1
    have htr : Commute (v*star v) t := (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))).1
    have htf : Commute (x*star v) t :=
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))).1
    have htd : Commute d t :=
      (hc _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))).1
    have hts : Supported p (p*t*p) :=
      ⟨by rw [← mul_assoc,← mul_assoc,hp.isIdempotentElem.eq],by rw [mul_assoc,hp.isIdempotentElem.eq]⟩
    have hcs (z : A) (hz : Supported p z) (hzt : Commute z t) : Commute (p*t*p) z := by
      have hpz : Commute p z := hz.1.trans hz.2.symm
      exact (hpz.mul_left hzt.symm).mul_left hpz
    have hLP : Commute (lift v (p*t*p)) p :=
      lift_commute_supported hp.isSelfAdjoint hvp ⟨hp.isIdempotentElem.eq,hp.isIdempotentElem.eq⟩
        (hts.2.trans hts.1.symm)
    have hLV := lift_commute_edge hpv hvp hvi hvr hts (hcs _ hrs htr)
    have hLVS := lift_commute_edge_star hp.isSelfAdjoint hpv hvp hvi hvr hts (hcs _ hrs htr)
    have hLF := lift_commute_supported hp.isSelfAdjoint hvp hfs (hcs _ hfs htf)
    have hx : x=(x*star v)*v := by rw [mul_assoc,hvi,hxr]
    have hLX : Commute (lift v (p*t*p)) x := by
      rw [hx]
      exact hLF.mul_right hLV
    have hLXS : Commute (lift v (p*t*p)) (star x) := by
      rw [hx,star_mul,hf.star_eq]
      exact hLVS.mul_right hLF
    have hLO : lift v (p*t*p)∈StarSubalgebra.centralizer ℂ (insert p {x+star x}) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      rintro y (rfl|hy)
      · exact ⟨hLP.symm.eq,by rw [hp.isSelfAdjoint.star_eq];exact hLP.symm.eq⟩
      · rcases hy with rfl
        exact ⟨(hLX.add_right hLXS).symm.eq,by
          rw [star_add,star_star,add_comm (star x) x];exact (hLX.add_right hLXS).symm.eq⟩
    have hLD : Commute (lift v (p*t*p)) d :=
      lift_commute_supported hp.isSelfAdjoint hvp hds (hcs _ hds htd)
    have hL : lift v (p*t*p)∈StarSubalgebra.centralizer ℂ
        (insert d (Bicommutant.algebra (insert p {x+star x}) : Set A)) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      rintro y (rfl|hy)
      · exact ⟨hLD.symm.eq,by rw [hd.star_eq];exact hLD.symm.eq⟩
      · exact ⟨((StarSubalgebra.mem_centralizer_iff ℂ).mp hy _ hLO).1.symm,
          ((StarSubalgebra.mem_centralizer_iff ℂ).mp (star_mem hy) _ hLO).1.symm⟩
    have he := ((StarSubalgebra.mem_centralizer_iff ℂ).mp ha _ hL).1
    rw [lift_mul_supported hvp has,supported_mul_lift hp.isSelfAdjoint hvp has] at he
    have htc : p*t*p=t*p := by rw [htp.eq,mul_assoc,hp.isIdempotentElem.eq]
    change t*a=a*t
    calc
      t*a=(t*p)*a := by rw [mul_assoc,has.1]
      _ = (p*t*p)*a := by rw [htc]
      _ = a*(p*t*p) := he
      _ = a*(t*p) := by rw [htc]
      _ = (a*p)*t := by rw [← htp.eq,mul_assoc]
      _ = a*t := by rw [has.2]
  rw [Bicommutant.algebra,StarSubalgebra.mem_centralizer_iff]
  intro t ht
  exact ⟨(htest t ht).eq,(htest (star t) (star_mem ht)).eq⟩
end FreeGroupFactorMain.CornerRerouting

namespace FreeGroupFactorMain.WeightedFock
open FreeFock
variable {ι : Type u_2} [DecidableEq ι]

theorem weightedDefect_semicircle_eq (u v : ℝ) (i j : ι) :
    weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)=
      (u:ℂ) • defectSemicircle u v i j := by
  simp only [weightedDefectCreation_eq,star_smul,Complex.star_def,Complex.conj_ofReal,
    defectSemicircle,smul_add]

theorem filled_corner_mem_diffuseBase (u v : ℝ) (hv : 0<v) (hvu : v<u) (i j : ι)
    (a : filledEdgeAlgebra u v i j) (ha : CornerRerouting.Supported P (a : Operator ι)) :
    (a : Operator ι)∈diffuseBase u v i j := by
  have hds : CornerRerouting.Supported P
      (weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)) := by
    rw [weightedDefect_semicircle_eq]
    exact ⟨by rw [mul_smul_comm,P_mul_defectSemicircle],
      by rw [smul_mul_assoc,defectSemicircle_mul_P]⟩
  have hh := CornerRerouting.filled_edge_corner_generated projection_P
    (edgePolar_left u v i) (edgePolar_right u v i) (edgePolar_initial u v hv.le hvu i)
    (offDiagonal_left u v i) (offDiagonal_right u v i) (leftModulus_selfAdjoint u v i)
    (IsSelfAdjoint.add_star_self (weightedDefectCreation u v i j)) hds a.property ha
  apply Bicommutant.generated_le (insert P {oldBaseGenerator u v i j})
    (insert P (insert (edgeRange u v i) (insert (leftModulus u v i)
      {weightedDefectCreation u v i j+star (weightedDefectCreation u v i j)}))) ?_ hh
  intro x hx
  rcases hx with rfl|hx
  · exact P_mem_diffuseBase u v i j
  rcases hx with rfl|hx
  · exact edgeRange_mem_diffuseBase u v hv hvu i j
  rcases hx with rfl|hx
  · exact leftModulus_mem_diffuseBase u v hv hvu i j
  rcases hx with rfl
  rw [weightedDefect_semicircle_eq]
  exact (diffuseBase u v i j).smul_mem (defectSemicircle_mem_diffuseBase u v hv hvu i j) _
end FreeGroupFactorMain.WeightedFock

end

namespace FreeGroupFactorMain.WeightedFock

section
open FreeFock Amplification CyclicSpectral
variable {ι : Type u_3} [DecidableEq ι]

theorem pRepresentation_mem_bicommutant (u v : ℝ) (i j : ι) (x : PCorner ι)
    (hx : (x:Operator ι)∈diffuseBase u v i j) :
    pRepresentation x∈Bicommutant.algebra ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι)) := by
  have hmul (a b : PCorner ι) : pRepresentation (a*b)=pRepresentation a*pRepresentation b :=
    (pRepresentation (ι := ι)).map_mul' a b
  have htest (B : PRange ι →L[ℂ] PRange ι)
      (hB : B∈StarSubalgebra.centralizer ℂ ({oldBaseOp u v i j} : Set (PRange ι →L[ℂ] PRange ι))) :
      B*pRepresentation x=pRepresentation x*B := by
    let b := (pRepresentation (ι := ι)).symm B
    have hbA : Commute (oldBaseCorner u v i j) b := by
      apply (pRepresentation (ι := ι)).injective
      change pRepresentation (oldBaseCorner u v i j*b)=pRepresentation (b*oldBaseCorner u v i j)
      rw [hmul,hmul]
      simpa only [StarAlgEquiv.apply_symm_apply,oldBaseOp,b] using
        ((StarSubalgebra.mem_centralizer_iff ℂ).mp hB _ (Set.mem_singleton _)).1
    have hb : (b:Operator ι)∈StarSubalgebra.centralizer ℂ (insert P {oldBaseGenerator u v i j}) := by
      rw [StarSubalgebra.mem_centralizer_iff]
      rintro T (rfl|hT)
      · exact ⟨b.property.1.trans b.property.2.symm,by
          rw [projection_P.isSelfAdjoint.star_eq];exact b.property.1.trans b.property.2.symm⟩
      · rcases hT with rfl
        have hh : oldBaseGenerator u v i j*(b:Operator ι)=(b:Operator ι)*oldBaseGenerator u v i j :=
          congrArg (fun z : PCorner ι => (z:Operator ι)) hbA.eq
        exact ⟨hh,by rw [(oldBaseGenerator_selfAdjoint u v i j).star_eq];exact hh⟩
    have hh : b*x=x*b := Subtype.ext (((StarSubalgebra.mem_centralizer_iff ℂ).mp hx _ hb).1)
    have he := congrArg (fun z : PCorner ι => pRepresentation z) hh
    rw [hmul,hmul] at he
    simpa only [StarAlgEquiv.apply_symm_apply,b] using he
  rw [Bicommutant.algebra,StarSubalgebra.mem_centralizer_iff]
  intro B hB
  exact ⟨htest B hB,htest (star B) (star_mem hB)⟩

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem representedBase_le_oldBase (hv : 0<v) (hvu : v<u) : representedBase u v ≤
    Bicommutant.algebra ({oldBaseOp u v (0:ℕ) 1} : Set (PRange ℕ →L[ℂ] PRange ℕ)) := by
  intro T hT
  have hh := filled_corner_mem_diffuseBase u v hv hvu (0:ℕ) 1
    (filledOfCorner ⟨(pRepresentation (ι := ℕ)).symm T,hT⟩)
    ((pRepresentation (ι := ℕ)).symm T).property
  simpa only [StarAlgEquiv.apply_symm_apply] using
    pRepresentation_mem_bicommutant u v (0:ℕ) 1 ((pRepresentation (ι := ℕ)).symm T) hh

theorem oldBaseOp_mem_weightedUniform : oldBaseOp u v (0:ℕ) 1∈
    Bicommutant.algebra (Set.range (weightedUniform u v hv hvu)) := by
  let : NormedRing (PRange ℕ →L[ℂ] PRange ℕ) := ContinuousLinearMap.toNormedRing
  let := oldBaseOp_noAtoms u v hv hvu
  have h := operator_mem_haar_bicommutant (oldBaseOp u v (0:ℕ) 1)
    (oldBaseOp_selfAdjoint u v 0 1) pRoot
    (Bicommutant.algebra ({oldBaseOp u v (0:ℕ) 1} : Set (PRange ℕ →L[ℂ] PRange ℕ)))
    (Set.isClosed_centralizer _)
    (Bicommutant.subset _ (Set.mem_singleton _))
    (oldBaseOp_commutant_total u v (hv.trans hvu).ne' hv.ne' (0:ℕ) 1)
  apply Bicommutant.mono _ (Set.range (weightedUniform u v hv hvu)) ?_ h
  intro T hT
  rcases hT with rfl
  exact ⟨uniformPhase,(uniformHom_phase (oldBaseOp u v (0:ℕ) 1)
    (oldBaseOp_selfAdjoint u v 0 1) pRoot).symm⟩

theorem representedBase_le_weightedUniform : representedBase u v ≤
    Bicommutant.algebra (Set.range (weightedUniform u v hv hvu)) := by
  apply (representedBase_le_oldBase u v hv hvu).trans
  apply Bicommutant.generated_le
  intro T hT
  rcases hT with rfl
  exact oldBaseOp_mem_weightedUniform u v hv hvu
end

section
open FreeFock Amplification WeightedCornerIndex
variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem absorbed_kind_recovery (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)
    (k : Kind) (hk : k.valid) : kindCreator u v k+star (kindCreator u v k.transpose)∈M := by
  have hh := ((cornerAbsorption u v hv hvu).output_generation M
    (fun i => hbase (kindLeft u v (description i)))
    (fun i => hbase (kindRight u v (description i)))).mpr hout
  have he := hh.1 (indexOf k)
  change kindCreator u v (description (indexOf k))+
    star (kindCreator u v (description (CircularRotation.flip (indexOf k))))∈M at he
  simpa only [description_flip,description_indexOf k hk] using he

theorem absorbed_raw_recovery (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)
    (n : ℕ) : pFresh u v 0 (n+2) false false+star (pFresh u v 0 (n+2) false false)∈M := by
  have hh := ((cornerAbsorption u v hv hvu).output_generation M
    (fun i => hbase (kindLeft u v (description i)))
    (fun i => hbase (kindRight u v (description i)))).mpr hout
  obtain ⟨⟨i,m⟩,h⟩ := reservoirCode.surjective n
  simpa only [cornerAbsorption,rawReservoir,h] using hh.2 i m

theorem absorbed_fresh_recovery (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)
    (n : ℕ) (r s : Bool) : pFresh u v 0 (n+2) r s+star (pFresh u v 0 (n+2) s r)∈M := by
  by_cases hh : r=false ∧ s=false
  · rcases hh with ⟨rfl,rfl⟩
    exact absorbed_raw_recovery u v hv hvu M hbase hout n
  · exact absorbed_kind_recovery u v hv hvu M hbase hout (.fresh n r s) hh

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

def blockCorner (u v : ℝ) (i j : ι) (r s : Bool) : PCorner ι :=
  sandwiched P projection_P (supportedLeg u v i r) (supportedLeg u v i s) (S u v j)
    (P_mul_supportedLeg u v i r) (P_mul_supportedLeg u v i s)

theorem blockCorner_normalized (u v : ℝ) (hu : u≠0) (i j : ι) (r s : Bool) :
    blockCorner u v i j r s=(u:ℂ) • (pFresh u v i j r s+star (pFresh u v i j s r)) := by
  apply Subtype.ext
  change supportedLeg u v i r*S u v j*star (supportedLeg u v i s)=
    (u:ℂ) • (normalizedCreation u v i j r s+star (normalizedCreation u v i j s r))
  simp only [normalizedCreation,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    ← smul_add (M := ℂ) (A := Operator ι)]
  rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul,supportedCreation_paired]

def residualBlockCorner (u v : ℝ) (i j : ι) (r s : Option Bool) : PCorner ι :=
  sandwiched P projection_P (residualLeg u v i r) (residualLeg u v i s) (S u v j)
    (P_mul_residualLeg u v i r) (P_mul_residualLeg u v i s)

theorem residualBlockCorner_normalized (u v : ℝ) (hu : u≠0) (i j : ι) (r s : Option Bool) :
    residualBlockCorner u v i j r s=(u:ℂ) • (pResidual u v i j r s+star (pResidual u v i j s r)) := by
  apply Subtype.ext
  change residualLeg u v i r*S u v j*star (residualLeg u v i s)=
    (u:ℂ) • (normalizedResidual u v i j r s+star (normalizedResidual u v i j s r))
  simp only [normalizedResidual,star_smul,Complex.star_def,map_inv₀,Complex.conj_ofReal,
    ← smul_add (M := ℂ) (A := Operator ι)]
  rw [smul_smul,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hu),one_smul]
  exact (residualPair_eq u v i j r s).symm

theorem blockCorner_zero_off (u v : ℝ) (i : ι) :
    (blockCorner u v i i false true : Operator ι)=leftModulus u v i := by
  change P*S u v i*star (edgePolar u v i)=_
  have h : (1-P)*star (edgePolar u v i)=star (edgePolar u v i) := by
    simpa only [star_mul,star_sub (R := Operator ι),star_one,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (edgePolar_right u v i)
  rw [leftModulus,offDiagonal, mul_assoc _ (1-P),h]

theorem blockCorner_star (u v : ℝ) (i j : ι) (r s : Bool) :
    star (blockCorner u v i j r s)=blockCorner u v i j s r := by
  apply Subtype.ext
  change star (supportedLeg u v i r*S u v j*star (supportedLeg u v i s))=_
  simp only [star_mul,star_star,(S_selfAdjoint u v j).star_eq,mul_assoc]
  rfl

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)
variable (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M)

include hbase in
theorem old_off_block_mem : blockCorner u v (0:ℕ) 0 false true∈M := by
  apply hbase ⟨blockCorner u v 0 0 false true,?_⟩
  change (blockCorner u v 0 0 false true : Operator ℕ)∈filledEdgeAlgebra u v 0 1
  rw [blockCorner_zero_off]
  exact edgeAlgebra_le_filled u v 0 1
    (mul_mem (offDiagonal_mem_edge u v 0) (star_mem (edgePolar_mem_edge u v 0)))

include hout hbase in
theorem absorbed_old_block_recovery (r s : Bool) : blockCorner u v 0 0 r s∈M := by
  have hu : u≠0 := (hv.trans hvu).ne'
  cases r <;> cases s
  · rw [blockCorner_normalized u v hu,← pDiagonal_eq_pFresh]
    exact M.smul_mem (absorbed_kind_recovery u v hv hvu M hbase hout (.diagonal false) trivial) _
  · exact old_off_block_mem u v M hbase
  · rw [← blockCorner_star u v 0 0 false true]
    exact star_mem (old_off_block_mem u v M hbase)
  · rw [blockCorner_normalized u v hu,← pDiagonal_eq_pFresh]
    exact M.smul_mem (absorbed_kind_recovery u v hv hvu M hbase hout (.diagonal true) trivial) _

include hbase hout in
theorem absorbed_residual_block_recovery (a b : Option Bool) :
    residualBlockCorner u v (0:ℕ) 1 a b∈M := by
  have hu : u≠0 := (hv.trans hvu).ne'
  by_cases hab : a=none ∧ b=none
  · rcases hab with ⟨rfl,rfl⟩
    apply hbase ⟨residualBlockCorner u v 0 1 none none,?_⟩
    change residualLeg u v (0:ℕ) none*S u v 1*star (residualLeg u v 0 none)∈filledEdgeAlgebra u v 0 1
    rw [← residualPair_eq,residualPair_none_none]
    exact (filledEdgeAlgebra u v 0 1).smul_mem (defectSemicircle_mem_filled u v hu 0 1) _
  · rw [residualBlockCorner_normalized u v hu]
    exact M.smul_mem (absorbed_kind_recovery u v hv hvu M hbase hout (.residual a b) hab) _

omit hv hvu M hbase hout in
theorem blockCorner_split_false_false : blockCorner u v (0:ℕ) 1 false false=
    residualBlockCorner u v 0 1 none none+residualBlockCorner u v 0 1 (some false) none+
    (residualBlockCorner u v 0 1 none (some false)+residualBlockCorner u v 0 1 (some false) (some false)) := by
  apply Subtype.ext
  change P*S u v 1*star P=_
  simp only [AddMemClass.coe_add,residualBlockCorner,sandwiched]
  rw [← residualLeg_sum u v (0:ℕ)]
  simp only [star_add (R := Operator ℕ),mul_add,add_mul]

omit hv hvu M hbase hout in
theorem blockCorner_split_false_true : blockCorner u v (0:ℕ) 1 false true=
    residualBlockCorner u v 0 1 none (some true)+residualBlockCorner u v 0 1 (some false) (some true) := by
  apply Subtype.ext
  change P*S u v 1*star (residualLeg u v 0 (some true))=_
  simp only [AddMemClass.coe_add,residualBlockCorner,sandwiched]
  rw [← residualLeg_sum u v (0:ℕ)]
  simp only [add_mul]

omit hv hvu M hbase hout in
theorem blockCorner_split_true_false : blockCorner u v (0:ℕ) 1 true false=
    residualBlockCorner u v 0 1 (some true) none+residualBlockCorner u v 0 1 (some true) (some false) := by
  apply Subtype.ext
  change residualLeg u v 0 (some true)*S u v 1*star P=_
  simp only [AddMemClass.coe_add,residualBlockCorner,sandwiched]
  rw [← residualLeg_sum u v (0:ℕ)]
  simp only [star_add (R := Operator ℕ),mul_add]

include hout hbase in
theorem absorbed_filled_block_recovery (r s : Bool) : blockCorner u v 0 1 r s∈M := by
  have hres := absorbed_residual_block_recovery u v hv hvu M hbase hout
  cases r <;> cases s
  · rw [blockCorner_split_false_false]
    exact add_mem (add_mem (hres _ _) (hres _ _)) (add_mem (hres _ _) (hres _ _))
  · rw [blockCorner_split_false_true];exact add_mem (hres _ _) (hres _ _)
  · rw [blockCorner_split_true_false];exact add_mem (hres _ _) (hres _ _)
  · exact hres (some true) (some true)

include hout hbase in
theorem absorbed_block_recovery (j : ℕ) (r s : Bool) : blockCorner u v 0 j r s∈M := by
  rcases j with _|(_|n)
  · exact absorbed_old_block_recovery u v hv hvu M hbase hout r s
  · exact absorbed_filled_block_recovery u v hv hvu M hbase hout r s
  · rw [blockCorner_normalized u v (hv.trans hvu).ne']
    exact M.smul_mem (absorbed_fresh_recovery u v hv hvu M hbase hout n r s) _
end

open FreeFock Amplification WeightedCornerIndex GaussianRecognition
variable {ι : Type u_6} [DecidableEq ι]

 theorem full_corner_commutant (u v : ℝ) (hv : 0<v) (hvu : v<u) (i₀ : ι)
    (X T : Operator ι) (hX : X ∈ ambientAlgebra u v)
    (hXs : CornerRerouting.Supported P X) (hT : CornerRerouting.Supported P T)
    (hR : Commute T (edgeRange u v i₀))
    (hA : ∀ i, Commute T (CornerRerouting.diagonal P (S u v i)))
    (hB : ∀ i, Commute T (CornerRerouting.offDiagonal P (edgePolar u v i₀) (S u v i)))
    (hBs : ∀ i, Commute T (star (CornerRerouting.offDiagonal P (edgePolar u v i₀) (S u v i))))
    (hC : ∀ i, Commute T (CornerRerouting.remaining P (edgePolar u v i₀) (S u v i))) :
    Commute T X :=
  CornerRerouting.corner_bicommutant projection_P (edgePolar_left u v i₀)
    (edgePolar_right u v i₀) (edgePolar_initial u v hv.le hvu i₀)
    hX hXs hT (S_selfAdjoint u v) hR hA hB hBs hC

theorem blockCorner_diagonal (u v : ℝ) (i j : ι) :
    (blockCorner u v i j false false : Operator ι)=CornerRerouting.diagonal P (S u v j) := by
  change P*S u v j*star P=P*S u v j*P
  rw [projection_P.isSelfAdjoint.star_eq]

theorem blockCorner_off (u v : ℝ) (i j : ι) :
    (blockCorner u v i j false true : Operator ι)=CornerRerouting.offDiagonal P (edgePolar u v i) (S u v j) := by
  change P*S u v j*star (edgePolar u v i)=P*S u v j*(1-P)*star (edgePolar u v i)
  have hh : (1-P)*star (edgePolar u v i)=star (edgePolar u v i) := by
    simpa only [star_mul,star_sub (R := Operator ι),star_one,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (edgePolar_right u v i)
  rw [mul_assoc _ (1-P),hh]

theorem blockCorner_remaining (u v : ℝ) (i j : ι) :
    (blockCorner u v i j true true : Operator ι)=CornerRerouting.remaining P (edgePolar u v i) (S u v j) := by
  change edgePolar u v i*S u v j*star (edgePolar u v i)=
    edgePolar u v i*(1-P)*S u v j*(1-P)*star (edgePolar u v i)
  have hh : (1-P)*star (edgePolar u v i)=star (edgePolar u v i) := by
    simpa only [star_mul,star_sub (R := Operator ι),star_one,projection_P.isSelfAdjoint.star_eq]
      using congrArg star (edgePolar_right u v i)
  rw [edgePolar_right,mul_assoc _ (1-P),hh]

variable (u v : ℝ) (hv : 0<v) (hvu : v<u)

theorem pAmbient_recovered (M : StarSubalgebra ℂ (PCorner ℕ))
    (hbase : ∀ a : Base u v,(a:PCorner ℕ)∈M)
    (hout : ∀ i n,(cornerAbsorption u v hv hvu).output i n+
      star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M) :
    pAmbient u v ≤ StarSubalgebra.centralizer ℂ
      (StarSubalgebra.centralizer ℂ (M : Set (PCorner ℕ)) : Set (PCorner ℕ)) := by
  intro X hX
  have htest (T : PCorner ℕ) (hT : T∈StarSubalgebra.centralizer ℂ (M : Set (PCorner ℕ))) : T*X=X*T := by
    have hc (a : PCorner ℕ) (ha : a∈M) : Commute (T:Operator ℕ) (a:Operator ℕ) :=
      (congrArg (fun b : PCorner ℕ => (b:Operator ℕ))
        (((StarSubalgebra.mem_centralizer_iff ℂ).mp hT a ha).1)).symm
    have hblocks (j : ℕ) (r s : Bool) := hc (blockCorner u v 0 j r s)
      (absorbed_block_recovery u v hv hvu M hbase hout j r s)
    apply Subtype.ext
    apply full_corner_commutant u v hv hvu (0:ℕ) (X:Operator ℕ) (T:Operator ℕ) hX X.property T.property
    · exact hc (pSupport u v 0 1 true) (hbase (pSupport u v 0 1 true))
    · intro j;rw [← blockCorner_diagonal u v 0 j];exact hblocks j false false
    · intro j;rw [← blockCorner_off u v 0 j];exact hblocks j false true
    · intro j
      rw [← blockCorner_off u v 0 j]
      exact hc (star (blockCorner u v 0 j false true))
        (star_mem (absorbed_block_recovery u v hv hvu M hbase hout j false true))
    · intro j;rw [← blockCorner_remaining u v 0 j];exact hblocks j true true
  rw [StarSubalgebra.mem_centralizer_iff]
  intro T hT
  exact ⟨htest T hT,htest (star T) (star_mem hT)⟩
end FreeGroupFactorMain.WeightedFock

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

theorem representedAmbient_le_weightedGenerated : representedAmbient u v≤(weightedSystem u v hv hvu).generated scalarFlip := by
  let G := (weightedSystem u v hv hvu).generated scalarFlip
  let M := G.comap (pRepresentation (ι := ℕ)).toStarAlgHom
  have hbase (a : Base u v) : (a:PCorner ℕ)∈M := by
    apply Bicommutant.mono (Set.range (weightedUniform u v hv hvu))
        ((weightedSystem u v hv hvu).generators scalarFlip) (fun _ h => Or.inl h)
    apply representedBase_le_weightedUniform u v hv hvu
    change (pRepresentation (ι := ℕ)).symm (pRepresentation a.val)∈Base u v
    simpa only [StarAlgEquiv.symm_apply_apply] using a.property
  have hout (i : WeightedCornerIndex.Index) (n : ℕ) :
      (cornerAbsorption u v hv hvu).output i n+
        star ((cornerAbsorption u v hv hvu).output (CircularRotation.flip i) n)∈M := by
    change pRepresentation (_+star _)∈G
    rw [pRep_add,pRep_star]
    exact Bicommutant.subset ((weightedSystem u v hv hvu).generators scalarFlip)
      (Or.inr (Set.mem_range_self (i,n)))
  intro T hT
  have hr := pAmbient_recovered u v hv hvu M hbase hout hT
  have hh := (bicommutant_transport (A := PCorner ℕ) (B := PRange ℕ →L[ℂ] PRange ℕ) (pRepresentation (ι := ℕ)) (M : Set (PCorner ℕ))
    ((pRepresentation (ι := ℕ)).symm T)).mpr hr
  rw [StarAlgEquiv.apply_symm_apply] at hh
  apply Bicommutant.generated_le ((weightedSystem u v hv hvu).generators scalarFlip)
    (pRepresentation '' (M : Set (PCorner ℕ))) ?_ hh
  rintro _ ⟨b,hb,rfl⟩
  exact hb

end FreeGroupFactorMain.WeightedFock

end

end OAI
end

theorem solution : type_of% @OAI.FreeGroupFactorMain.WeightedFock.representedAmbient_le_weightedGenerated := @OAI.FreeGroupFactorMain.WeightedFock.representedAmbient_le_weightedGenerated
