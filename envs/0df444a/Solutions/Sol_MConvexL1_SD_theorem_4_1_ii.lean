-- Prove2me | solution 1 for MConvexL1.SD.theorem_4_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:38:19.77083+00:00
-- url     : https://prove2.me/submissions/b61b83ab-d8ef-4807-941b-28f4d89ed824

import Definitions.Def_DiscreteConvex_Algorithms_L1Dist
import Definitions.Def_DiscreteConvex_MConvexFunctions_ArgMin
import Definitions.Def_DiscreteConvex_MConvexFunctions_CharVec
import Definitions.Def_DiscreteConvex_MConvexFunctions_DomZ
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppPos
import Definitions.Def_DiscreteConvex_MConvexFunctions_SuppNeg
import Definitions.Def_DiscreteConvex_MConvexFunctions_MExchangeAxiom
import Definitions.Def_DiscreteConvex_MConvexFunctions_MNatExchangeAxiom
import Definitions.Def_MConvexL1_SD_Basic
import Init
import Mathlib










section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem scalar_balancing (a b c : ℤ) (h : b<a) :
    (a-1-c).natAbs+(b+1-c).natAbs ≤ (a-c).natAbs+(b-c).natAbs := by
  omega

theorem between_distance_add (a b c : ℤ) (hu : a<b → b≤c) (hd : b<a → c≤b) :
    (a-b).natAbs+(b-c).natAbs=(a-c).natAbs := by
  omega

theorem distance_zero_iff {V : Type*} [Fintype V] (x y : V→ℤ) :
    L1Dist x y=0 ↔ x=y := by
  simp [L1Dist,Finset.sum_eq_zero_iff,funext_iff,sub_eq_zero]

theorem distance_symm {V : Type*} [Fintype V] (x y : V→ℤ) :
    L1Dist x y=L1Dist y x := by
  unfold L1Dist
  apply Finset.sum_congr rfl
  intro i hi
  omega

theorem no_outward_distance_add {V : Type*} [Fintype V] (x y c : V→ℤ)
    (hu : ∀ i,x i<y i → y i≤c i) (hd : ∀ i,y i<x i → c i≤y i) :
    L1Dist x y+L1Dist y c=L1Dist x c := by
  unfold L1Dist
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact between_distance_add _ _ _ (hu i) (hd i)
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem exchange_distance {V : Type*} [Fintype V] [DecidableEq V]
    (x y z : V→ℤ) (i j : V) (hi : i∈SuppPos x y) (hj : j∈SuppNeg x y) :
    L1Dist (fun w=>x w-CharVec i w+CharVec j w) z+
      L1Dist (fun w=>y w+CharVec i w-CharVec j w) z ≤ L1Dist x z+L1Dist y z := by
  have hip : y i<x i := by simpa [SuppPos] using hi
  have hjn : x j<y j := by simpa [SuppNeg] using hj
  have hij : i≠j := by intro h; subst j; omega
  unfold L1Dist
  rw [←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro w hw
  by_cases hwi : w=i
  · subst w
    simpa [CharVec,hij] using scalar_balancing (x i) (y i) (z i) hip
  · by_cases hwj : w=j
    · subst w
      simpa [CharVec,hij,Ne.symm hij,add_comm] using scalar_balancing (y j) (x j) (z j) hjn
    · simp [CharVec,hwi,hwj]
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

/-- Equal coordinate sums are unnecessary for the outward-direction conclusion. -/
theorem outward_direction {V : Type*} [Fintype V] [DecidableEq V]
    (c y yt : V→ℤ) (hne : y≠yt) (hdist : L1Dist y c≤L1Dist yt c) :
    (∃ i∈SuppPos yt y,c i<yt i) ∨ (∃ j∈SuppNeg yt y,yt j<c j) := by
  by_contra hn
  push_neg at hn
  have hu (i : V) (hi : y i<yt i) : yt i≤c i :=
    hn.1 i (by simpa [SuppPos] using hi)
  have hd (i : V) (hi : yt i<y i) : c i≤yt i :=
    hn.2 i (by simpa [SuppNeg] using hi)
  have hsum:=no_outward_distance_add y yt c hu hd
  have hz : L1Dist y yt=0 := by omega
  exact hne ((distance_zero_iff y yt).mp hz)
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem sum_sub_unit {V : Type*} [Fintype V] [DecidableEq V] (x : V→ℤ) (i : V) :
    (∑ w,(x w-CharVec i w))=(∑ w,x w)-1 := by
  simp [Finset.sum_sub_distrib,CharVec]

theorem sum_unit_exchange {V : Type*} [Fintype V] [DecidableEq V] (x : V→ℤ) (i j : V) :
    (∑ w,(x w-CharVec i w+CharVec j w))=∑ w,x w := by
  simp [Finset.sum_sub_distrib,Finset.sum_add_distrib,CharVec]

theorem negative_support_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V→ℤ) (hs : ∑w,x w=∑w,y w) (i : V) (hi : i∈SuppPos x y) :
    (SuppNeg x y).Nonempty := by
  by_contra hn
  have hle (w : V) : y w≤x w := by
    by_contra h
    exact hn ⟨w,by simpa [SuppNeg] using lt_of_not_ge h⟩
  have hlt : (∑w,y w)<∑w,x w := Finset.sum_lt_sum (fun w _=>hle w)
    ⟨i,Finset.mem_univ i,by simpa [SuppPos] using hi⟩
  omega

/-- The fixed-sum domain eliminates the unpaired branch of M-natural exchange. -/
theorem fixed_sum_exchange {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) : MExchangeAxiom f := by
  obtain ⟨hex,θ,hθ⟩:=hf
  intro x hx y hy i hi
  have hs : (∑w,x w)=∑w,y w := (hθ x hx).trans (hθ y hy).symm
  have hne:=negative_support_nonempty x y hs i hi
  have hout : f (fun w=>x w-CharVec i w)=⊤ := by
    by_contra hn
    have hm : (fun w=>x w-CharVec i w)∈DomZ f := hn
    have hh:=hθ _ hm
    rw [sum_sub_unit,hθ x hx] at hh
    omega
  have hb:=hex x hx y hy i hi
  rw [hout,top_add,min_top_left] at hb
  obtain ⟨j,hj,he⟩:=Finset.exists_mem_eq_inf (SuppNeg x y) hne
    (fun j=>f (fun w=>x w-CharVec i w+CharVec j w)+f (fun w=>y w+CharVec i w-CharVec j w))
  exact ⟨j,hj,by simpa only [he] using hb⟩
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem towards_exchange_distance {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V→ℤ) (i j : V) (hi : i∈SuppPos x y) (hj : j∈SuppNeg x y) :
    L1Dist (fun w=>x w-CharVec i w+CharVec j w) y+2=L1Dist x y := by
  have hip : y i<x i := by simpa [SuppPos] using hi
  have hjn : x j<y j := by simpa [SuppNeg] using hj
  have hij : i≠j := by intro h; subst j; omega
  have he (w : V) :
      (x w-CharVec i w+CharVec j w-y w).natAbs+
        (if w=i then 1 else 0)+(if w=j then 1 else 0)=(x w-y w).natAbs := by
    by_cases hwi : w=i
    · subst w
      simp [CharVec,hij]
      omega
    · by_cases hwj : w=j
      · subst w
        simp [CharVec,Ne.symm hij]
        omega
      · simp [CharVec,hwi,hwj]
  have hh:=congrArg (fun f : V→ℕ=>∑w,f w) (funext he)
  simpa [Finset.sum_add_distrib,L1Dist] using hh

theorem outward_exchange_nonincrease {V : Type*} [Fintype V] [DecidableEq V]
    (x c : V→ℤ) (i j : V) (hi : c i<x i) (hij : i≠j) :
    L1Dist (fun w=>x w-CharVec i w+CharVec j w) c≤L1Dist x c := by
  have he (w : V) :
      (x w-CharVec i w+CharVec j w-c w).natAbs+(if w=i then 1 else 0)≤
        (x w-c w).natAbs+(if w=j then 1 else 0) := by
    by_cases hwi : w=i
    · subst w
      simp [CharVec,hij]
      omega
    · by_cases hwj : w=j
      · subst w
        simp [CharVec,Ne.symm hij]
        omega
      · simp [CharVec,hwi,hwj]
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun w _=>he w)
  simp only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true] at hh
  exact Nat.le_of_add_le_add_right hh
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem bounded_domain_finite {V : Type*} [Fintype V] (f : (V→ℤ)→WithTop ℝ)
    (hb : BddDom f) : (DomZ f).Finite := by
  obtain ⟨B,hB⟩:=hb
  have hp : {x : V→ℤ | ∀ i,x i∈Set.Icc (-B) B}.Finite :=
    Set.Finite.pi' (fun _=>Set.finite_Icc (-B) B)
  apply hp.subset
  intro x hx i
  exact abs_le.mp (hB x hx i)

theorem bounded_argmin_exists {V : Type*} [Fintype V] (f : (V→ℤ)→WithTop ℝ)
    (hb : BddDom f) (hne : (DomZ f).Nonempty) :
    ∃ x∈DomZ f,x∈ArgMin f := by
  obtain ⟨x,hx,hmin⟩:=Set.exists_min_image (DomZ f) f (bounded_domain_finite f hb) hne
  refine ⟨x,hx,?_⟩
  intro y
  by_cases hy : y∈DomZ f
  · exact hmin y hy
  · have ht : f y=⊤ := by simpa [DomZ] using hy
    rw [ht]
    exact le_top

theorem bounded_radius_min_exists {V : Type*} [Fintype V] (f : (V→ℤ)→WithTop ℝ)
    (hb : BddDom f) (c : V→ℤ) (k : ℕ)
    (hne : ∃ x∈DomZ f,L1Dist x c≤2*k) : (Mset f c k).Nonempty := by
  let S : Set (V→ℤ):={x|x∈DomZ f ∧ L1Dist x c≤2*k}
  have hfin : S.Finite := (bounded_domain_finite f hb).subset (fun _ h=>h.1)
  obtain ⟨x,hx,hmin⟩:=Set.exists_min_image S f hfin (by obtain ⟨y,hy,hd⟩:=hne; exact ⟨y,hy,hd⟩)
  exact ⟨x,hx.1,hx.2,fun y hy hd=>hmin y ⟨hy,hd⟩⟩

theorem initial_radius_min_exists {V : Type*} [Fintype V] (f : (V→ℤ)→WithTop ℝ)
    (hb : BddDom f) (c : V→ℤ) (σ : ℕ)
    (hσ : IsLeast {d|∃x∈DomZ f,L1Dist x c=d} (2*σ)) :
    (Mset f c σ).Nonempty := by
  obtain ⟨x,hx,hd⟩:=hσ.1
  exact bounded_radius_min_exists f hb c σ ⟨x,hx,hd.le⟩

/-- Once a ball contains a global minimizer, its constrained optima are global. -/
theorem radius_optima_global {V : Type*} [Fintype V] (f : (V→ℤ)→WithTop ℝ)
    (c : V→ℤ) (k : ℕ) (y : V→ℤ) (hy : y∈DomZ f) (hymin : y∈ArgMin f)
    (hyd : L1Dist y c≤2*k) {x : V→ℤ} (hx : x∈Mset f c k) : x∈ArgMin f := by
  intro z
  exact (hx.2.2 y hy hyd).trans (hymin z)

theorem global_min_in_ball {V : Type*} [Fintype V] (f : (V→ℤ)→WithTop ℝ)
    (c : V→ℤ) (k : ℕ) {x : V→ℤ} (hx : x∈DomZ f) (hmin : x∈ArgMin f)
    (hd : L1Dist x c≤2*k) : x∈Mset f c k := ⟨hx,hd,fun y _ _=>hmin y⟩
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem distance_neg {V : Type*} [Fintype V] (x y : V→ℤ) :
    L1Dist (fun w=>-x w) (fun w=>-y w)=L1Dist x y := by
  unfold L1Dist
  apply Finset.sum_congr rfl
  intro w hw
  change (-x w- -y w).natAbs=(x w-y w).natAbs
  omega

theorem outward_increase_exchange_nonincrease {V : Type*} [Fintype V] [DecidableEq V]
    (x c : V→ℤ) (i j : V) (hj : x j<c j) (hij : i≠j) :
    L1Dist (fun w=>x w-CharVec i w+CharVec j w) c≤L1Dist x c := by
  have h:=outward_exchange_nonincrease (fun w=>-x w) (fun w=>-c w) j i (by omega) (Ne.symm hij)
  have he : (fun w=>-x w-CharVec j w+CharVec i w)=
      (fun w=>-(x w-CharVec i w+CharVec j w)) := by funext w; ring
  rw [he,distance_neg,distance_neg] at h
  exact h

theorem distance_decomposition {V : Type*} [Fintype V] (x y : V→ℤ) :
    (L1Dist x y:ℤ)=(∑w,(x w-y w))+2*∑w,((y w-x w).toNat:ℤ) := by
  have he (w : V) : ((x w-y w).natAbs:ℤ)=(x w-y w)+2*((y w-x w).toNat:ℤ) := by omega
  simp only [L1Dist,Nat.cast_sum,he,Finset.sum_add_distrib,←Finset.mul_sum]

theorem balanced_distance_twice {V : Type*} [Fintype V] (x y : V→ℤ)
    (hs : ∑w,x w=∑w,y w) : L1Dist x y=2*∑w,(y w-x w).toNat := by
  have h:=distance_decomposition x y
  rw [Finset.sum_sub_distrib,hs,sub_self,zero_add] at h
  exact_mod_cast h

theorem balanced_distance_even {V : Type*} [Fintype V] (x y : V→ℤ)
    (hs : ∑w,x w=∑w,y w) : Even (L1Dist x y) := by
  rw [balanced_distance_twice x y hs]
  exact even_two_mul _
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius.Controls
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem equal_coordinates_exchange_can_increase :
    L1Dist (fun w : Fin 2=>0-CharVec (0:Fin 2) w+CharVec (1:Fin 2) w) (fun _=>0)+
      L1Dist (fun w : Fin 2=>0+CharVec (0:Fin 2) w-CharVec (1:Fin 2) w) (fun _=>0)=4 ∧
    L1Dist (fun _ : Fin 2=>0) (fun _=>0)+L1Dist (fun _ : Fin 2=>0) (fun _=>0)=0 := by
  norm_num [L1Dist,CharVec,Fin.sum_univ_two]

theorem distance_hypothesis_needed :
    let y : Fin 2→ℤ:=![2,-2]
    let yt : Fin 2→ℤ:=![1,-1]
    (∑i,y i)=(∑i,yt i) ∧ y≠yt ∧
      ¬ ((∃i∈SuppPos yt y,0<yt i) ∨ (∃j∈SuppNeg yt y,yt j<0)) := by
  dsimp
  constructor
  · norm_num [Fin.sum_univ_two]
  constructor
  · intro h
    have hh:=congrArg (fun f : Fin 2→ℤ=>f 0) h
    norm_num at hh
  · norm_num [SuppPos,SuppNeg,Fin.exists_fin_two]

theorem no_equal_sum_needed :
    (∑i : Fin 1,(![0] : Fin 1→ℤ) i)≠∑i : Fin 1,(![1] : Fin 1→ℤ) i ∧
      ((∃i∈SuppPos (![1] : Fin 1→ℤ) ![0],0<(![1] : Fin 1→ℤ) i) ∨
        (∃j∈SuppNeg (![1] : Fin 1→ℤ) ![0],(![1] : Fin 1→ℤ) j<0)) := by
  norm_num [SuppPos,SuppNeg]
end Queelius.MConvexRadius.Controls

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem exchange_domain_left {V : Type*} (f : (V→ℤ)→WithTop ℝ)
    (x y a b : V→ℤ) (hx : x∈DomZ f) (hy : y∈DomZ f)
    (h : f a+f b≤f x+f y) : a∈DomZ f := by
  change f a≠⊤
  intro ha
  rw [ha,top_add] at h
  have hsum : f x+f y≠⊤ := by
    exact WithTop.add_ne_top.mpr ⟨hx,hy⟩
  exact hsum (top_le_iff.mp h)

theorem exchange_same_sum {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MExchangeAxiom f) (y : V→ℤ) (hy : y∈DomZ f) :
    ∀ x∈DomZ f,(∑w,x w)=∑w,y w := by
  have aux (d : ℕ) : ∀x∈DomZ f,L1Dist x y=d → (∑w,x w)=∑w,y w := by
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro x hx hd
      by_cases hp : (SuppPos x y).Nonempty
      · obtain ⟨i,hi⟩:=hp
        obtain ⟨j,hj,hex⟩:=hf x hx y hy i hi
        let a:=fun w=>x w-CharVec i w+CharVec j w
        let b:=fun w=>y w+CharVec i w-CharVec j w
        have ha : a∈DomZ f := exchange_domain_left f x y a b hx hy hex
        have hstep:=towards_exchange_distance x y i j hi hj
        have hlt : L1Dist a y<d := by dsimp [a]; omega
        have hs:=ih (L1Dist a y) hlt a ha rfl
        simpa only [a,sum_unit_exchange] using hs
      · have hle (w : V) : x w≤y w := by
          by_contra h
          exact hp ⟨w,by simpa [SuppPos] using lt_of_not_ge h⟩
        have heq : x=y := by
          funext w
          by_contra hne
          have hwle:=hle w
          have hw : w∈SuppPos y x := by simp only [SuppPos,Finset.mem_filter,Finset.mem_univ,true_and]; omega
          obtain ⟨j,hj,_⟩:=hf y hy x hx w hw
          have hlt : y j<x j := by simpa [SuppNeg] using hj
          exact not_lt_of_ge (hle j) hlt
        rw [heq]
  intro x hx
  exact aux (L1Dist x y) x hx rfl

theorem paired_exchange_implies_mconvex {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MExchangeAxiom f) : MConvex f := by
  refine ⟨?_,?_⟩
  · intro x hx y hy i hi
    obtain ⟨j,hj,hex⟩:=hf x hx y hy i hi
    exact (min_le_right _ _).trans ((Finset.inf_le hj).trans hex)
  · by_cases hn : (DomZ f).Nonempty
    · obtain ⟨y,hy⟩:=hn
      exact ⟨∑w,y w,exchange_same_sum f hf y hy⟩
    · exact ⟨0,fun x hx=>False.elim (hn ⟨x,hx⟩)⟩

theorem exchange_characterization {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) : MConvex f ↔ MExchangeAxiom f :=
  ⟨fixed_sum_exchange f,paired_exchange_implies_mconvex f⟩
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

/-- Finite exchange inputs force both exchanged values to be finite. -/
theorem exchange_values_finite (a b c d : WithTop ℝ) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : c+d≤a+b) : c≠⊤ ∧ d≠⊤ := by
  have hab : a+b≠⊤ := WithTop.add_ne_top.mpr ⟨ha,hb⟩
  have hcd : c+d≠⊤ := ne_top_of_le_ne_top hab h
  exact WithTop.add_ne_top.mp hcd

theorem exchange_strict_value (a b c d : WithTop ℝ) (ha : a ≠ ⊤) (hb : b ≠ ⊤)
    (h : c+d≤a+b) (hc : a<c) : d<b := by
  obtain ⟨hcfin,hdfin⟩:=exchange_values_finite a b c d ha hb h
  lift a to ℝ using ha
  lift b to ℝ using hb
  lift c to ℝ using hcfin
  lift d to ℝ using hdfin
  norm_cast at h hc ⊢
  linarith

theorem positive_support_nonempty {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V→ℤ) (hs : ∑w,x w=∑w,y w) (hne : x≠y) : (SuppPos x y).Nonempty := by
  by_contra hn
  have hle (i : V) : x i≤y i := by
    by_contra h
    exact hn ⟨i,by simpa [SuppPos] using lt_of_not_ge h⟩
  have he : ∀ i,x i=y i := by
    intro i
    by_contra h
    have hi : x i<y i := lt_of_le_of_ne (hle i) h
    have hsum := Finset.sum_lt_sum (fun w (_ : w∈(Finset.univ : Finset V))=>hle w)
      ⟨i,Finset.mem_univ i,hi⟩
    omega
  exact hne (funext he)

/-- A nearest global minimizer supplies a strictly improving exchange at every nonglobal point. -/
theorem nearest_global_descent {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (y xs : V→ℤ)
    (hy : y∈DomZ f) (hxs : xs∈DomZ f) (hmin : xs∈ArgMin f)
    (hnear : ∀ x∈ArgMin f,L1Dist xs y≤L1Dist x y) (hne : y≠xs) :
    ∃ i∈SuppPos y xs,∃ j∈SuppNeg y xs,
      f (fun w=>y w-CharVec i w+CharVec j w)<f y := by
  obtain ⟨θ,hθ⟩:=hf.2
  obtain ⟨i,hi⟩:=positive_support_nonempty y xs ((hθ y hy).trans (hθ xs hxs).symm) hne
  obtain ⟨j,hj,hex⟩:=fixed_sum_exchange f hf y hy xs hxs i hi
  let z := fun w=>xs w+CharVec i w-CharVec j w
  have hdz : L1Dist z y+2=L1Dist xs y := by
    have h:=towards_exchange_distance xs y j i (by simpa [SuppPos,SuppNeg] using hj)
      (by simpa [SuppPos,SuppNeg] using hi)
    have he : (fun w=>xs w-CharVec j w+CharVec i w)=z := by funext w; dsimp [z]; ring
    rwa [he] at h
  have hstrict : f xs<f z := by
    refine lt_of_le_of_ne (hmin z) ?_
    intro he
    have hzmin : z∈ArgMin f := by intro x; rw [←he]; exact hmin x
    have hd:=hnear z hzmin
    omega
  have hswap : f z+f (fun w=>y w-CharVec i w+CharVec j w)≤f xs+f y := by
    simpa only [add_comm] using hex
  exact ⟨i,hi,j,hj,exchange_strict_value _ _ _ _ hxs hy hswap hstrict⟩

/-- Bounded effective domain gives a nearest global minimizer. -/
theorem nearest_global_exists {V : Type*} [Fintype V]
    (f : (V→ℤ)→WithTop ℝ) (hb : BddDom f) (y : V→ℤ) (hy : y∈DomZ f) :
    ∃ xs∈DomZ f,xs∈ArgMin f ∧ ∀ x∈ArgMin f,L1Dist xs y≤L1Dist x y := by
  have hsub : ArgMin f⊆DomZ f := by
    intro x hx
    exact ne_top_of_le_ne_top hy (hx y)
  have hfin : (ArgMin f).Finite := (bounded_domain_finite f hb).subset hsub
  obtain ⟨x,hx,hm⟩:=bounded_argmin_exists f hb ⟨y,hy⟩
  obtain ⟨xs,hxs,hn⟩:=Set.exists_min_image (ArgMin f) (fun x=>L1Dist x y) hfin ⟨x,hm⟩
  exact ⟨xs,hsub hxs,hxs,hn⟩

theorem nonglobal_descent {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f)
    (y : V→ℤ) (hy : y∈DomZ f) (hn : y∉ArgMin f) :
    ∃ i j : V,f (fun w=>y w-CharVec i w+CharVec j w)<f y := by
  obtain ⟨xs,hxs,hmin,hnear⟩:=nearest_global_exists f hb y hy
  have hne : y≠xs := by intro he; exact hn (he.symm ▸ hmin)
  obtain ⟨i,hi,j,hj,hd⟩:=nearest_global_descent f hf y xs hy hxs hmin hnear hne
  exact ⟨i,j,hd⟩
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius.Controls
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

/-- The platform convention admits the empty effective domain; the root's least-radius
hypothesis separately supplies a feasible point. -/
theorem empty_domain_convention {V : Type*} [Fintype V] [DecidableEq V] :
    MConvex (fun _ : V→ℤ=>(⊤:WithTop ℝ)) ∧ DomZ (fun _ : V→ℤ=>(⊤:WithTop ℝ))=∅ := by
  constructor
  · apply paired_exchange_implies_mconvex
    intro x hx
    simp [DomZ] at hx
  · ext x
    simp [DomZ]

/-- A full integer line does not have the fixed-sum domain required by paired exchange. -/
theorem full_line_not_paired_exchange :
    ¬ MExchangeAxiom (fun _ : Fin 1→ℤ=>(0:WithTop ℝ)) := by
  intro h
  have hx : (fun _ : Fin 1=>(1:ℤ))∈DomZ (fun _ : Fin 1→ℤ=>(0:WithTop ℝ)) := by simp [DomZ]
  have hy : (fun _ : Fin 1=>(0:ℤ))∈DomZ (fun _ : Fin 1→ℤ=>(0:WithTop ℝ)) := by simp [DomZ]
  have hi : (0:Fin 1)∈SuppPos (fun _=>(1:ℤ)) (fun _=>0) := by simp [SuppPos]
  obtain ⟨j,hj,_⟩:=h _ hx _ hy 0 hi
  simp [SuppNeg] at hj
end Queelius.MConvexRadius.Controls

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem exchange_radius_bound {V : Type*} [Fintype V] [DecidableEq V]
    (x c : V→ℤ) (i j : V) :
    L1Dist (fun w=>x w-CharVec i w+CharVec j w) c≤L1Dist x c+2 := by
  have he (w : V) : (x w-CharVec i w+CharVec j w-c w).natAbs≤
      (x w-c w).natAbs+(if w=i then 1 else 0)+(if w=j then 1 else 0) := by
    by_cases hi : w=i <;> by_cases hj : w=j <;> simp [CharVec,hi,hj] <;> omega
  have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun w _=>he w)
  simpa [Finset.sum_add_distrib,L1Dist] using hh

theorem radius_optima_exist_above_initial {V : Type*} [Fintype V]
    (f : (V→ℤ)→WithTop ℝ) (hb : BddDom f) (c : V→ℤ) (σ k : ℕ)
    (hσ : IsLeast {d|∃x∈DomZ f,L1Dist x c=d} (2*σ)) (hk : σ≤k) :
    (Mset f c k).Nonempty := by
  obtain ⟨x,hx,hd⟩:=hσ.1
  exact bounded_radius_min_exists f hb c k ⟨x,hx,by omega⟩

theorem radius_below_tau_nonglobal {V : Type*} [Fintype V]
    (f : (V→ℤ)→WithTop ℝ) (c : V→ℤ) (τ : ℕ)
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ))
    (y : V→ℤ) (hd : L1Dist y c<2*τ) : y∉ArgMin f := by
  intro hm
  have h:=hτ.2 ⟨y,hm,rfl⟩
  omega

/-- One improving exchange fits in the next ball, so adjacent optimal values strictly drop. -/
theorem adjacent_values_strict {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f)
    (c : V→ℤ) (τ : ℕ)
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ))
    (k : ℕ) (hk : k<τ) (y yp : V→ℤ)
    (hy : y∈Mset f c k) (hyp : yp∈Mset f c (k+1)) : f yp<f y := by
  have hn:=radius_below_tau_nonglobal f c τ hτ y (by have:=hy.2.1; omega)
  obtain ⟨i,j,hi⟩:=nonglobal_descent f hf hb y hy.1 hn
  have hz : (fun w=>y w-CharVec i w+CharVec j w)∈DomZ f :=
    ne_top_of_lt hi
  have hd:=exchange_radius_bound y c i j
  have hc:=hy.2.1
  exact lt_of_le_of_lt (hyp.2.2 _ hz (by omega)) hi

/-- Parity and local descent exclude slack in every ball up to the first global optimum. -/
theorem radius_optima_on_sphere {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f)
    (c : V→ℤ) (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (τ : ℕ)
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ))
    (k : ℕ) (hk : k≤τ) (x : V→ℤ) (hx : x∈Mset f c k) : L1Dist x c=2*k := by
  by_contra hn
  have hd : L1Dist x c<2*k := lt_of_le_of_ne hx.2.1 hn
  have hng:=radius_below_tau_nonglobal f c τ hτ x (by omega)
  obtain ⟨i,j,hi⟩:=nonglobal_descent f hf hb x hx.1 hng
  have hz : (fun w=>x w-CharVec i w+CharVec j w)∈DomZ f := ne_top_of_lt hi
  have hpar:=balanced_distance_twice x c (hs x hx.1)
  have hbnd:=exchange_radius_bound x c i j
  have hball : L1Dist (fun w=>x w-CharVec i w+CharVec j w) c≤2*k := by omega
  exact (not_lt_of_ge (hx.2.2 _ hz hball)) hi

/-- Local optimality against every unit exchange is equivalent to global optimality. -/
theorem local_global_iff {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f)
    (y : V→ℤ) (hy : y∈DomZ f) :
    y∈ArgMin f ↔ ∀ i j : V,f y≤f (fun w=>y w-CharVec i w+CharVec j w) := by
  constructor
  · intro h i j; exact h _
  · intro h
    by_contra hn
    obtain ⟨i,j,hi⟩:=nonglobal_descent f hf hb y hy hn
    exact (not_lt_of_ge (h i j)) hi
end Queelius.MConvexRadius

end

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms

open MConvexL1.SD

theorem geometry_solution {V : Type*} [Fintype V] [DecidableEq V] (x y z : V → ℤ) (i j : V)
    (hi : i ∈ SuppPos x y) (hj : j ∈ SuppNeg x y) :
    L1Dist x z + L1Dist y z ≥
      L1Dist (fun w => x w - CharVec i w + CharVec j w) z +
        L1Dist (fun w => y w + CharVec i w - CharVec j w) z := by
  exact Queelius.MConvexRadius.exchange_distance x y z i j hi hj




namespace MConvexL1.SD

theorem lemma_A_1 {V : Type*} [Fintype V] [DecidableEq V] (xc y yt : V → ℤ) (hne : y ≠ yt)
    (hsum : ∑ v, y v = ∑ v, yt v) (hdist : L1Dist y xc ≤ L1Dist yt xc) :
    (∃ i ∈ SuppPos yt y, xc i < yt i) ∨ (∃ j ∈ SuppNeg yt y, yt j < xc j) := by
  exact Queelius.MConvexRadius.outward_direction xc y yt hne hdist

end MConvexL1.SD


namespace MConvexL1.SD

theorem m_exc_iff {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ) :
    MConvex f ↔ MExchangeAxiom f := by
  exact Queelius.MConvexRadius.exchange_characterization f

end MConvexL1.SD


end

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms
namespace MConvexL1.SD

theorem theorem_4_1_i {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (σ τ : ℕ) (hσ : IsLeast {d | ∃ x ∈ DomZ f, L1Dist x xc = d} (2 * σ))
    (hτ : IsLeast {d | ∃ x ∈ ArgMin f, L1Dist x xc = d} (2 * τ)) :
    (∀ k, σ ≤ k → k ≤ τ → (Mset f xc k).Nonempty) ∧
    (∀ k, σ ≤ k → k < τ → ∀ y ∈ Mset f xc k, ∀ y' ∈ Mset f xc (k + 1), f y' < f y) ∧
    (∀ k, σ ≤ k → k ≤ τ → ∀ x ∈ Mset f xc k, L1Dist x xc = 2 * k)  := by
  refine ⟨?_,?_,?_⟩
  · intro k hk _
    exact Queelius.MConvexRadius.radius_optima_exist_above_initial f hbdd xc σ k hσ hk
  · intro k _ hk y hy yp hyp
    exact Queelius.MConvexRadius.adjacent_values_strict f hf hbdd xc τ hτ k hk y yp hy hyp
  · intro k _ hk x hx
    exact Queelius.MConvexRadius.radius_optima_on_sphere f hf hbdd xc hxc τ hτ k hk x hx

end MConvexL1.SD

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

theorem exchange_tight_values (a b c d : WithTop ℝ) (ha : a≠⊤) (hb : b≠⊤)
    (hex : c+d≤a+b) (hc : a≤c) (hd : b≤d) : c=a ∧ d=b := by
  obtain ⟨hcf,hdf⟩:=exchange_values_finite a b c d ha hb hex
  lift a to ℝ using ha
  lift b to ℝ using hb
  lift c to ℝ using hcf
  lift d to ℝ using hdf
  norm_cast at hex hc hd ⊢
  constructor <;> linarith

theorem outward_exchange_exists {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (c x y : V→ℤ)
    (hx : x∈DomZ f) (hy : y∈DomZ f) (hneq : y≠x) (hd : L1Dist y c≤L1Dist x c) :
    ∃ i∈SuppPos x y,∃ j∈SuppNeg x y,
      L1Dist (fun w=>x w-CharVec i w+CharVec j w) c≤L1Dist x c ∧
      f (fun w=>x w-CharVec i w+CharVec j w)+
      f (fun w=>y w+CharVec i w-CharVec j w)≤f x+f y := by
  rcases outward_direction c y x hneq hd with ⟨i,hi,hic⟩|⟨j,hj,hjc⟩
  · obtain ⟨j,hj,he⟩:=fixed_sum_exchange f hf x hx y hy i hi
    have hij : i≠j := by
      have hip : y i<x i := by simpa [SuppPos] using hi
      have hjn : x j<y j := by simpa [SuppNeg] using hj
      intro h; subst j; omega
    exact ⟨i,hi,j,hj,outward_exchange_nonincrease x c i j hic hij,he⟩
  · obtain ⟨i,hi,he⟩:=fixed_sum_exchange f hf y hy x hx j (by simpa [SuppPos,SuppNeg] using hj)
    have hip : y i<x i := by simpa [SuppNeg] using hi
    have hjn : x j<y j := by simpa [SuppNeg] using hj
    have hij : i≠j := by intro h; subst j; omega
    have e₁ : (fun w=>y w-CharVec j w+CharVec i w)=(fun w=>y w+CharVec i w-CharVec j w) := by funext w; ring
    have e₂ : (fun w=>x w+CharVec j w-CharVec i w)=(fun w=>x w-CharVec i w+CharVec j w) := by funext w; ring
    refine ⟨i,by simpa [SuppPos] using hip,j,hj,outward_increase_exchange_nonincrease x c i j hjc hij,?_⟩
    simpa only [e₁,e₂,add_comm] using he

theorem reverse_exchange_distance {V : Type*} [Fintype V] [DecidableEq V]
    (x y : V→ℤ) (i j : V) (hi : i∈SuppPos x y) (hj : j∈SuppNeg x y) :
    L1Dist (fun w=>y w+CharVec i w-CharVec j w) x+2=L1Dist y x := by
  have h:=towards_exchange_distance y x j i (by simpa [SuppPos,SuppNeg] using hj)
    (by simpa [SuppPos,SuppNeg] using hi)
  have he : (fun w=>y w-CharVec j w+CharVec i w)=(fun w=>y w+CharVec i w-CharVec j w) := by funext w; ring
  rwa [he] at h

theorem exchange_increase_direction {V : Type*} [Fintype V] [DecidableEq V]
    (x c : V→ℤ) (i j : V)
    (hd : L1Dist (fun w=>x w+CharVec i w-CharVec j w) c=L1Dist x c+2) :
    i∉SuppNeg x c ∧ j∉SuppPos x c := by
  have hij : i≠j := by
    intro he; subst j
    simp only [add_sub_cancel_right] at hd
    change L1Dist x c=L1Dist x c+2 at hd
    omega
  have he : (fun w=>x w-CharVec j w+CharVec i w)=(fun w=>x w+CharVec i w-CharVec j w) := by funext w; ring
  constructor
  · intro hi
    have h:=outward_increase_exchange_nonincrease x c j i (by simpa [SuppNeg] using hi) (Ne.symm hij)
    rw [he,hd] at h
    omega
  · intro hj
    have h:=outward_exchange_nonincrease x c j i (by simpa [SuppPos] using hj) (Ne.symm hij)
    rw [he,hd] at h
    omega

theorem exchange_decrease_direction {V : Type*} [Fintype V] [DecidableEq V]
    (x c : V→ℤ) (i j : V)
    (hd : L1Dist (fun w=>x w-CharVec i w+CharVec j w) c+2=L1Dist x c) :
    i∈SuppPos x c ∧ j∈SuppNeg x c := by
  let z := fun w=>x w-CharVec i w+CharVec j w
  have hij : i≠j := by
    intro he; subst j
    simp only [sub_add_cancel] at hd
    change L1Dist x c+2=L1Dist x c at hd
    omega
  have he : (fun w=>z w+CharVec i w-CharVec j w)=x := by funext w; dsimp [z]; ring
  have hrev : L1Dist (fun w=>z w+CharVec i w-CharVec j w) c=L1Dist z c+2 := by rw [he]; exact hd.symm
  obtain ⟨hi,hj⟩:=exchange_increase_direction z c i j hrev
  have hzi : c i≤z i := by simpa [SuppNeg] using hi
  have hzj : z j≤c j := by simpa [SuppPos] using hj
  simp [z,CharVec,hij,Ne.symm hij] at hzi hzj
  constructor
  · simp only [SuppPos,Finset.mem_filter,Finset.mem_univ,true_and]; omega
  · simp only [SuppNeg,Finset.mem_filter,Finset.mem_univ,true_and]; omega
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

/-- Choosing either endpoint nearest to the other forces an optimal adjacent pair. -/
theorem adjacent_exchange_pair {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (c : V→ℤ)
    (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (k : ℕ) (x y : V→ℤ)
    (hx : x∈Mset f c (k+1)) (hy : y∈Mset f c k)
    (hdx : L1Dist x c=2*(k+1)) (hdy : L1Dist y c=2*k)
    (hn : (∀z∈Mset f c (k+1),L1Dist x y≤L1Dist z y) ∨
          (∀z∈Mset f c k,L1Dist y x≤L1Dist z x)) :
    ∃ i∈SuppPos x y,∃ j∈SuppNeg x y,
      (fun w=>x w-CharVec i w+CharVec j w)∈Mset f c k ∧
      (fun w=>y w+CharVec i w-CharVec j w)∈Mset f c (k+1) := by
  have hne : y≠x := by intro he; rw [he,hdx] at hdy; omega
  obtain ⟨i,hi,j,hj,hd,hex⟩:=outward_exchange_exists f hf c x y hx.1 hy.1 hne (by omega)
  let z := fun w=>x w-CharVec i w+CharVec j w
  let w := fun v=>y v+CharVec i v-CharVec j v
  obtain ⟨hzf,hwf⟩:=exchange_values_finite _ _ _ _ hx.1 hy.1 hex
  have hzdom : z∈DomZ f := hzf
  have hwdom : w∈DomZ f := hwf
  have hdist:=exchange_distance x y c i j hi hj
  have hzball : L1Dist z c≤2*k := by
    by_contra hnot
    have hp:=balanced_distance_twice z c (hs z hzdom)
    have hzeq : L1Dist z c=2*(k+1) := by change L1Dist z c≤L1Dist x c at hd; omega
    have hwball : L1Dist w c≤2*k := by change L1Dist z c+L1Dist w c≤_ at hdist; omega
    have hvals:=exchange_tight_values _ _ _ _ hx.1 hy.1 hex
      (hx.2.2 z hzdom hzeq.le) (hy.2.2 w hwdom hwball)
    have hzm : z∈Mset f c (k+1) := ⟨hzdom,hzeq.le,fun v hv hdv=>by rw [hvals.1]; exact hx.2.2 v hv hdv⟩
    have hwm : w∈Mset f c k := ⟨hwdom,hwball,fun v hv hdv=>by rw [hvals.2]; exact hy.2.2 v hv hdv⟩
    rcases hn with hn|hn
    · have hnear:=hn z hzm
      have hstep:=towards_exchange_distance x y i j hi hj
      change L1Dist z y+2=L1Dist x y at hstep
      omega
    · have hnear:=hn w hwm
      have hstep:=reverse_exchange_distance x y i j hi hj
      change L1Dist w x+2=L1Dist y x at hstep
      omega
  have hwball : L1Dist w c≤2*(k+1) := by
    have h:=exchange_radius_bound y c j i
    have he : (fun v=>y v-CharVec j v+CharVec i v)=w := by funext v; dsimp [w]; ring
    rw [he,hdy] at h
    omega
  have hswap : f z+f w≤f y+f x := by simpa only [add_comm] using hex
  have hvals:=exchange_tight_values _ _ _ _ hy.1 hx.1 hswap
    (hy.2.2 z hzdom hzball) (hx.2.2 w hwdom hwball)
  refine ⟨i,hi,j,hj,⟨hzdom,hzball,?_⟩,⟨hwdom,hwball,?_⟩⟩
  · intro v hv hdv; rw [hvals.1]; exact hy.2.2 v hv hdv
  · intro v hv hdv; rw [hvals.2]; exact hx.2.2 v hv hdv

theorem nearest_radius_optimum {V : Type*} [Fintype V]
    (f : (V→ℤ)→WithTop ℝ) (hb : BddDom f) (c y : V→ℤ) (k : ℕ)
    (hne : (Mset f c k).Nonempty) :
    ∃x∈Mset f c k,∀z∈Mset f c k,L1Dist x y≤L1Dist z y := by
  exact Set.exists_min_image (Mset f c k) (fun x=>L1Dist x y)
    ((bounded_domain_finite f hb).subset (fun _ h=>h.1)) hne

theorem adjacent_outward_optimum {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f) (c : V→ℤ)
    (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (σ τ : ℕ)
    (hσ : IsLeast {d|∃x∈DomZ f,L1Dist x c=d} (2*σ))
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ))
    (k : ℕ) (hk : σ≤k) (hkt : k<τ) (y : V→ℤ) (hy : y∈Mset f c k) :
    ∃ i j : V,i∉SuppNeg y c ∧ j∉SuppPos y c ∧
      (fun w=>y w+CharVec i w-CharVec j w)∈Mset f c (k+1) := by
  obtain ⟨x,hx,hn⟩:=nearest_radius_optimum f hb c y (k+1)
    (radius_optima_exist_above_initial f hb c σ (k+1) hσ (by omega))
  have hdx:=radius_optima_on_sphere f hf hb c hs τ hτ (k+1) (by omega) x hx
  have hdy:=radius_optima_on_sphere f hf hb c hs τ hτ k (by omega) y hy
  obtain ⟨i,hi,j,hj,hz,hw⟩:=adjacent_exchange_pair f hf c hs k x y hx hy hdx hdy (Or.inl hn)
  have hdw:=radius_optima_on_sphere f hf hb c hs τ hτ (k+1) (by omega) _ hw
  obtain ⟨hni,hnj⟩:=exchange_increase_direction y c i j (by omega)
  exact ⟨i,j,hni,hnj,hw⟩

theorem adjacent_inward_optimum {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f) (c : V→ℤ)
    (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (σ τ : ℕ)
    (hσ : IsLeast {d|∃x∈DomZ f,L1Dist x c=d} (2*σ))
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ))
    (k : ℕ) (hk : σ≤k) (hkt : k<τ) (x : V→ℤ) (hx : x∈Mset f c (k+1)) :
    ∃ i∈SuppPos x c,∃ j∈SuppNeg x c,
      (fun w=>x w-CharVec i w+CharVec j w)∈Mset f c k := by
  obtain ⟨y,hy,hn⟩:=nearest_radius_optimum f hb c x k
    (radius_optima_exist_above_initial f hb c σ k hσ hk)
  have hdx:=radius_optima_on_sphere f hf hb c hs τ hτ (k+1) (by omega) x hx
  have hdy:=radius_optima_on_sphere f hf hb c hs τ hτ k (by omega) y hy
  obtain ⟨i,hi,j,hj,hz,hw⟩:=adjacent_exchange_pair f hf c hs k x y hx hy hdx hdy (Or.inr hn)
  have hdz:=radius_optima_on_sphere f hf hb c hs τ hτ k (by omega) _ hz
  obtain ⟨hpi,hnj⟩:=exchange_decrease_direction x c i j (by omega)
  exact ⟨i,hpi,j,hnj,hz⟩
end Queelius.MConvexRadius

end

section
namespace Queelius.MConvexRadius
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

/-- The nearest global optimum has an even distance from a center on the fixed-sum hyperplane. -/
theorem nearest_global_radius_exists {V : Type*} [Fintype V]
    (f : (V→ℤ)→WithTop ℝ) (hb : BddDom f) (c : V→ℤ)
    (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (hne : (DomZ f).Nonempty) :
    ∃ τ : ℕ,IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ) := by
  obtain ⟨y,hy⟩:=hne
  have hsub : ArgMin f⊆DomZ f := by
    intro x hx; exact ne_top_of_le_ne_top hy (hx y)
  obtain ⟨z,hz,hm⟩:=bounded_argmin_exists f hb ⟨y,hy⟩
  obtain ⟨xs,hxs,hnear⟩:=Set.exists_min_image (ArgMin f) (fun x=>L1Dist x c)
    ((bounded_domain_finite f hb).subset hsub) ⟨z,hm⟩
  let τ := ∑v,(c v-xs v).toNat
  have hd : L1Dist xs c=2*τ := balanced_distance_twice xs c (hs xs (hsub hxs))
  refine ⟨τ,⟨xs,hxs,hd⟩,?_⟩
  intro d hdmem
  obtain ⟨x,hx,rfl⟩:=hdmem
  rw [←hd]
  exact hnear x hx

theorem radius_optimum_after_tau_global {V : Type*} [Fintype V]
    (f : (V→ℤ)→WithTop ℝ) (c : V→ℤ) (τ k : ℕ)
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ)) (hk : τ≤k)
    (y : V→ℤ) (hy : y∈Mset f c k) : y∈ArgMin f := by
  obtain ⟨xs,hxs,hd⟩:=hτ.1
  have hdom : xs∈DomZ f := ne_top_of_le_ne_top hy.1 (hxs y)
  exact radius_optima_global f c k xs hdom hxs (by omega) hy

/-- Every minimum-value unit move from a radius-k optimum is a radius-(k+1) optimum. -/
theorem steepest_step_optimal {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f) (c : V→ℤ)
    (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (σ τ : ℕ)
    (hσ : IsLeast {d|∃x∈DomZ f,L1Dist x c=d} (2*σ))
    (hτ : IsLeast {d|∃x∈ArgMin f,L1Dist x c=d} (2*τ))
    (k : ℕ) (hk : σ≤k) (y : V→ℤ) (hy : y∈Mset f c k) (i j : V)
    (hbest : ∀ p q : V,f (fun w=>y w+CharVec i w-CharVec j w)≤
      f (fun w=>y w+CharVec p w-CharVec q w)) :
    (fun w=>y w+CharVec i w-CharVec j w)∈Mset f c (k+1) := by
  have hex : ∃ p q : V,(fun w=>y w+CharVec p w-CharVec q w)∈Mset f c (k+1) := by
    by_cases hkt : k<τ
    · obtain ⟨p,q,_,_,hm⟩:=adjacent_outward_optimum f hf hb c hs σ τ hσ hτ k hk hkt y hy
      exact ⟨p,q,hm⟩
    · have hglobal:=radius_optimum_after_tau_global f c τ k hτ (by omega) y hy
      have hm:=global_min_in_ball f c (k+1) hy.1 hglobal (by have:=hy.2.1; omega)
      refine ⟨i,i,?_⟩
      simpa only [add_sub_cancel_right] using hm
  obtain ⟨p,q,hw⟩:=hex
  have hle:=hbest p q
  have hz : (fun w=>y w+CharVec i w-CharVec j w)∈DomZ f := ne_top_of_le_ne_top hw.1 hle
  have hbnd:=exchange_radius_bound y c j i
  have he : (fun w=>y w-CharVec j w+CharVec i w)=(fun w=>y w+CharVec i w-CharVec j w) := by funext w; ring
  rw [he] at hbnd
  exact ⟨hz,by have:=hy.2.1; omega,fun z hzd hzb=>hle.trans (hw.2.2 z hzd hzb)⟩

theorem all_run_iterates_optimal {V : Type*} [Fintype V] [DecidableEq V]
    (f : (V→ℤ)→WithTop ℝ) (hf : MConvex f) (hb : BddDom f) (c : V→ℤ)
    (hs : ∀x∈DomZ f,∑v,x v=∑v,c v) (σ γ : ℕ)
    (hσ : IsLeast {d|∃x∈DomZ f,L1Dist x c=d} (2*σ))
    (x : ℕ→V→ℤ) (hrun : IsSDRun f c σ γ x) :
    ∀ k,σ≤k→k≤γ→x k∈Mset f c k := by
  have hne : (DomZ f).Nonempty := ⟨x σ,hrun.1.1⟩
  obtain ⟨τ,hτ⟩:=nearest_global_radius_exists f hb c hs hne
  intro k hk
  induction k,hk using Nat.le_induction with
  | base => intro _; exact hrun.1
  | succ k hk ih =>
    intro hkg
    obtain ⟨i,j,hbest,he⟩:=hrun.2 (k+1) (by omega) hkg
    have hprev : x k∈Mset f c k := ih (by omega)
    simp only [Nat.add_sub_cancel] at hbest he
    rw [he]
    exact steepest_step_optimal f hf hb c hs σ τ hσ hτ k hk (x k) hprev i j hbest
end Queelius.MConvexRadius

end

section
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms
namespace MConvexL1.SD

theorem theorem_4_1_ii {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (σ τ : ℕ) (hσ : IsLeast {d | ∃ x ∈ DomZ f, L1Dist x xc = d} (2 * σ))
    (hτ : IsLeast {d | ∃ x ∈ ArgMin f, L1Dist x xc = d} (2 * τ)) :
    ∀ k, σ ≤ k → k < τ → ∀ y ∈ Mset f xc k, ∃ i j : V, i ∉ SuppNeg y xc ∧ j ∉ SuppPos y xc ∧
      (fun w => y w + CharVec i w - CharVec j w) ∈ Mset f xc (k + 1) := by
  exact Queelius.MConvexRadius.adjacent_outward_optimum f hf hbdd xc hxc σ τ hσ hτ

end MConvexL1.SD

namespace MConvexL1.SD

theorem theorem_4_1_iii {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (σ τ : ℕ) (hσ : IsLeast {d | ∃ x ∈ DomZ f, L1Dist x xc = d} (2 * σ))
    (hτ : IsLeast {d | ∃ x ∈ ArgMin f, L1Dist x xc = d} (2 * τ)) :
    ∀ k, σ ≤ k → k < τ → ∀ y ∈ Mset f xc (k + 1), ∃ i ∈ SuppPos y xc, ∃ j ∈ SuppNeg y xc,
      (fun w => y w - CharVec i w + CharVec j w) ∈ Mset f xc k := by
  exact Queelius.MConvexRadius.adjacent_inward_optimum f hf hbdd xc hxc σ τ hσ hτ

end MConvexL1.SD

namespace MConvexL1.SD

theorem theorem_4_2 {V : Type*} [Fintype V] [DecidableEq V] (f : (V → ℤ) → WithTop ℝ)
    (hf : MConvex f) (hbdd : BddDom f) (xc : V → ℤ)
    (hxc : ∀ x ∈ DomZ f, ∑ v, x v = ∑ v, xc v)
    (σ γ : ℕ) (hσ : IsLeast {d | ∃ x ∈ DomZ f, L1Dist x xc = d} (2 * σ)) (hγ : σ ≤ γ)
    (x : ℕ → V → ℤ) (hrun : IsSDRun f xc σ γ x) :
    (∀ k, σ ≤ k → k ≤ γ → x k ∈ Mset f xc k) ∧ x γ ∈ Mset f xc γ := by
  have h:=Queelius.MConvexRadius.all_run_iterates_optimal f hf hbdd xc hxc σ γ hσ x hrun
  exact ⟨h,h γ hγ le_rfl⟩

end MConvexL1.SD


end

section
namespace Queelius.MConvexRadius.Controls
open DiscreteConvex.MConvexFunctions DiscreteConvex.Algorithms MConvexL1.SD

/-- A nonconvex valley on three points defeats the local-to-global inference. -/
def valley (x : Fin 2→ℤ) : WithTop ℝ :=
  if x=![0,0] then 1 else if x=![1,-1] then 2 else if x=![2,-2] then 0 else ⊤

theorem valley_local : ∀ i j : Fin 2,
    valley ![0,0]≤valley (fun w=>![0,0] w-CharVec i w+CharVec j w) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [valley,CharVec,funext_iff,Fin.forall_fin_two]

theorem valley_nonglobal : ![0,0]∉ArgMin valley := by
  intro h
  have hh:=h ![2,-2]
  norm_num [valley,funext_iff,Fin.forall_fin_two] at hh
  have hh' : (1:ℝ)≤0 := WithTop.coe_le_coe.mp hh
  linarith

theorem valley_not_mconvex : ¬MConvex valley := by
  intro h
  have hx : ![2,-2]∈DomZ valley := by norm_num [DomZ,valley,funext_iff,Fin.forall_fin_two]
  have hy : ![0,0]∈DomZ valley := by norm_num [DomZ,valley]
  obtain ⟨j,hj,he⟩:=Queelius.MConvexRadius.fixed_sum_exchange valley h ![2,-2] hx ![0,0] hy 0
    (by norm_num [SuppPos])
  fin_cases j <;> norm_num [SuppNeg] at hj
  norm_num [valley,CharVec,funext_iff,Fin.forall_fin_two] at he

/-- A center off the domain hyperplane can have odd distance; the even-radius argument needs its hypothesis. -/
theorem off_hyperplane_odd :
    L1Dist (![0,0] : Fin 2→ℤ) ![1,0]=1 ∧
    (∑v:Fin 2,(![0,0] : Fin 2→ℤ) v)≠∑v:Fin 2,(![1,0] : Fin 2→ℤ) v := by
  norm_num [L1Dist,Fin.sum_univ_two]
end Queelius.MConvexRadius.Controls

end

section
universe audit_u0
theorem submission_primary_solution :
∀ {V : Type audit_u0} [inst : Fintype V] [inst_1 : DecidableEq V] (f : (V → Int) → WithTop Real),
  @MConvexL1.SD.MConvex V inst inst_1 f →
    @MConvexL1.SD.BddDom V f →
      ∀ (xc : V → Int),
        (∀ (x : V → Int),
            @Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                (@DiscreteConvex.MConvexFunctions.DomZ V f) x →
              @Eq Int (@Finset.sum V Int Int.instAddCommMonoid (@Finset.univ V inst) fun (v : V) => x v)
                (@Finset.sum V Int Int.instAddCommMonoid (@Finset.univ V inst) fun (v : V) => xc v)) →
          ∀ (σ γ : Nat),
            @IsLeast Nat instLENat
                (@Set.ofPred Nat fun (d : Nat) =>
                  @Exists (V → Int) fun (x : V → Int) =>
                    And
                      (@Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                        (@DiscreteConvex.MConvexFunctions.DomZ V f) x)
                      (@Eq Nat (@DiscreteConvex.Algorithms.L1Dist V inst x xc) d))
                (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                  (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) σ) →
              @LE.le Nat instLENat σ γ →
                ∀ (x : Nat → V → Int),
                  @MConvexL1.SD.IsSDRun V inst inst_1 f xc σ γ x →
                    And
                      (∀ (k : Nat),
                        @LE.le Nat instLENat σ k →
                          @LE.le Nat instLENat k γ →
                            @Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                              (@MConvexL1.SD.Mset V inst f xc k) (x k))
                      (@Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                        (@MConvexL1.SD.Mset V inst f xc γ) (x γ)) := @MConvexL1.SD.theorem_4_2

end

universe audit_u0

theorem solution : (
  ∀ {V : Type audit_u0} [inst : Fintype V] [inst_1 : DecidableEq V] (f : (V → Int) → WithTop Real),
    @MConvexL1.SD.MConvex V inst inst_1 f →
      @MConvexL1.SD.BddDom V f →
        ∀ (xc : V → Int),
          (∀ (x : V → Int),
              @Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                  (@DiscreteConvex.MConvexFunctions.DomZ V f) x →
                @Eq Int (@Finset.sum V Int Int.instAddCommMonoid (@Finset.univ V inst) fun (v : V) => x v)
                  (@Finset.sum V Int Int.instAddCommMonoid (@Finset.univ V inst) fun (v : V) => xc v)) →
            ∀ (σ τ : Nat),
              @IsLeast Nat instLENat
                  (@Set.ofPred Nat fun (d : Nat) =>
                    @Exists (V → Int) fun (x : V → Int) =>
                      And
                        (@Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                          (@DiscreteConvex.MConvexFunctions.DomZ V f) x)
                        (@Eq Nat (@DiscreteConvex.Algorithms.L1Dist V inst x xc) d))
                  (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                    (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) σ) →
                @IsLeast Nat instLENat
                    (@Set.ofPred Nat fun (d : Nat) =>
                      @Exists (V → Int) fun (x : V → Int) =>
                        And
                          (@Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                            (@DiscreteConvex.MConvexFunctions.ArgMin V f) x)
                          (@Eq Nat (@DiscreteConvex.Algorithms.L1Dist V inst x xc) d))
                    (@HMul.hMul Nat Nat Nat (@instHMul Nat instMulNat)
                      (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) τ) →
                  ∀ (k : Nat),
                    @LE.le Nat instLENat σ k →
                      @LT.lt Nat instLTNat k τ →
                        ∀ (y : V → Int),
                          @Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                              (@MConvexL1.SD.Mset V inst f xc k) y →
                            @Exists V fun (i : V) =>
                              @Exists V fun (j : V) =>
                                And
                                  (Not
                                    (@Membership.mem V (Finset V)
                                      (@SetLike.instMembership (Finset V) V (@Finset.instSetLike V))
                                      (@DiscreteConvex.MConvexFunctions.SuppNeg V inst inst_1 y xc) i))
                                  (And
                                    (Not
                                      (@Membership.mem V (Finset V)
                                        (@SetLike.instMembership (Finset V) V (@Finset.instSetLike V))
                                        (@DiscreteConvex.MConvexFunctions.SuppPos V inst inst_1 y xc) j))
                                    (@Membership.mem (V → Int) (Set (V → Int)) (@Set.instMembership (V → Int))
                                      (@MConvexL1.SD.Mset V inst f xc
                                        (@HAdd.hAdd Nat Nat Nat (@instHAdd Nat instAddNat) k
                                          (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))
                                      fun (w : V) =>
                                      @HSub.hSub Int Int Int (@instHSub Int Int.instSub)
                                        (@HAdd.hAdd Int Int Int (@instHAdd Int Int.instAdd) (y w)
                                          (@DiscreteConvex.MConvexFunctions.CharVec V inst_1 i w))
                                        (@DiscreteConvex.MConvexFunctions.CharVec V inst_1 j w)))
) := @MConvexL1.SD.theorem_4_1_ii
