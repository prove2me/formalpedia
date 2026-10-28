-- Prove2me | solution 1 for OAI.Kadison.CornerPhase.exists_relative_corner_phase
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:52:27.615862+00:00
-- url     : https://prove2.me/submissions/9600a795-35c1-4abf-98ff-3357d54e099d

import Mathlib
import Definitions.Def_OAIQ039C066

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPhaseAveraging
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.CornerPhase

section Fourier

variable {N : ℕ} [NeZero N]

lemma character_sum (a : ZMod N) :
    (∑ m : ZMod N, ZMod.stdAddChar (a*m))=if a=0 then (N:ℂ) else 0 := by
  classical
  split_ifs with ha
  · simp [ha]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N ha)

lemma character_orthogonality (i j : ZMod N) :
    (∑ m : ZMod N, star (ZMod.stdAddChar (i*m))*ZMod.stdAddChar (j*m))=
      if i=j then (N:ℂ) else 0 := by
  classical
  have hs (a : ZMod N) : star (ZMod.stdAddChar a)=ZMod.stdAddChar (-a) := by
    rw [AddChar.map_neg_eq_inv]
    exact ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).inv_apply_eq_conj a).symm
  simp only [hs,←AddChar.map_add_eq_mul,←sub_eq_neg_add,←sub_mul]
  rw [character_sum]
  congr 1
  exact propext (sub_eq_zero.trans eq_comm)

lemma phase_parseval (b : ZMod N → ℂ) :
    (∑ m : ZMod N, ‖phaseSum b m‖^2)=(N:ℝ)*∑ j, ‖b j‖^2 := by
  classical
  have h : (∑ m : ZMod N, star (phaseSum b m)*phaseSum b m)=
      (N:ℂ)*∑ j, star (b j)*b j := by
    simp only [phaseSum,star_sum,star_mul,Finset.sum_mul_sum]
    calc
      _=∑ i : ZMod N, ∑ j : ZMod N,
          (star (b i)*b j)*(∑ m : ZMod N, star (ZMod.stdAddChar (i*m))*ZMod.stdAddChar (j*m)) := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      _=(N:ℂ)*∑ j, star (b j)*b j := by
        simp only [character_orthogonality]
        simp [Finset.sum_ite_eq,Finset.mul_sum,mul_comm]
  have hnorm (z : ℂ) : star z*z=((‖z‖^2:ℝ):ℂ) := by
    rw [Complex.sq_norm]
    exact Complex.normSq_eq_conj_mul_self.symm
  simp only [hnorm,←Complex.ofReal_sum,←Complex.ofReal_natCast,←Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

lemma phase_parseval_mul [Fact N.Prime] (b : ZMod N → ℂ) (k : ZMod N) (hk : k≠0) :
    (∑ m : ZMod N, ‖phaseSum b (k*m)‖^2)=(N:ℝ)*∑ j, ‖b j‖^2 := by
  rw [←phase_parseval b]
  exact Fintype.sum_equiv (Equiv.mulLeft₀ k hk) _ _ (fun _ => rfl)

end Fourier

section Algebra

variable {A : Type*} [CStarAlgebra A]

variable {I : Type*} [Fintype I]

variable (e : I → A) (he : ∀ i, IsStarProjection (e i))
  (ho : ∀ i j, i≠j → e i*e j=0)

include he ho in
lemma diagonal_mul (c d : I → ℂ) :
    diagonal e c*diagonal e d=diagonal e (fun i => c i*d i) := by
  simp only [diagonal,Finset.sum_mul_sum,smul_mul_assoc,mul_smul_comm,smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · rw [(he i).isIdempotentElem.eq,mul_comm]
  · intro j _ hji
    rw [ho i j hji.symm,smul_zero]
  · simp

include he in
lemma diagonal_star (c : I → ℂ) : star (diagonal e c)=diagonal e (fun i => star (c i)) := by
  simp only [diagonal,star_sum,star_smul,(he _).isSelfAdjoint.star_eq]

include he ho in
lemma diagonal_pow_succ (c : I → ℂ) (k : ℕ) :
    diagonal e c^(k+1)=diagonal e (fun i => c i^(k+1)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ,ih,diagonal_mul e he ho]
    simp only [pow_succ]

include he ho in
lemma diagonal_support (c : I → ℂ) :
    diagonal e c*(∑ i,e i)=diagonal e c ∧ (∑ i,e i)*diagonal e c=diagonal e c := by
  have hq : (∑ i,e i)=diagonal e (fun _ => 1) := by simp [diagonal]
  rw [hq,diagonal_mul e he ho,diagonal_mul e he ho]
  simp

include he ho in
lemma diagonal_unitary (c : I → ℂ) (hc : ∀ i, ‖c i‖=1) :
    star (diagonal e c)*diagonal e c=∑ i,e i ∧
      diagonal e c*star (diagonal e c)=∑ i,e i := by
  have hc' (i : I) : star (c i)*c i=1 := by
    change (starRingEnd ℂ) (c i)*c i=1
    rw [←Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq,hc i]
    norm_num
  rw [diagonal_star e he,diagonal_mul e he ho,diagonal_mul e he ho]
  constructor
  · simp only [hc',diagonal,one_smul]
  · simp only [mul_comm (c _) (star (c _)),hc',diagonal,one_smul]

end Algebra

end Kadison.CornerPhase

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_TracialL2Tools
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace

namespace Kadison.TracialL2

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ)

lemma norm_nonneg (a : A) : 0≤norm τ a := _root_.norm_nonneg _

lemma norm_sq (a : A) : norm τ a^2=(τ (star a*a)).re := by
  rw [norm,InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℂ)]
  rfl

lemma norm_mul_left (a b : A) : norm τ (a*b)≤‖a‖*norm τ b := by
  change ‖τ.leftMulMapPreGNS a (τ.toPreGNS b)‖≤‖a‖*‖τ.toPreGNS b‖
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (LinearMap.mkContinuous_norm_le _ (_root_.norm_nonneg _) _) (_root_.norm_nonneg _))

variable (hτ : ∀ a b : A,τ (a*b)=τ (b*a))

include hτ in
lemma norm_star (a : A) : norm τ (star a)=norm τ a := by
  apply (sq_eq_sq₀ (norm_nonneg τ _) (norm_nonneg τ _)).mp
  rw [norm_sq,norm_sq,star_star,hτ]

include hτ in
lemma norm_trace_mul (a b : A) : ‖τ (a*b)‖≤norm τ a*norm τ b := by
  have h := norm_inner_le_norm (𝕜:=ℂ) (τ.toPreGNS (star a)) (τ.toPreGNS b)
  change ‖τ (star (star a)*b)‖≤norm τ (star a)*norm τ b at h
  simpa only [star_star,norm_star τ hτ] using h

lemma norm_projection_sq {p : A} (hp : IsStarProjection p) : norm τ p^2=(τ p).re := by
  rw [norm_sq,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq]

end Kadison.TracialL2

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_CornerPhaseSelectionCore
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators

namespace Kadison.CornerPhase

open TracialL2

section Trace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (τ : A →ₚ[ℂ] ℂ) (hτ : ∀ a b : A, τ (a*b)=τ (b*a))

include hτ in
lemma trace_projection_mul_le (e a : A) (he : IsStarProjection e) :
    ‖τ (e*a)‖ ≤ (τ e).re*‖a‖ := by
  have ht : τ (e*a)=τ (e*(a*e)) := by
    calc
      _=τ (a*e) := hτ _ _
      _=τ ((a*e)*e) := by rw [mul_assoc,he.isIdempotentElem.eq]
      _=_ := hτ _ _
  rw [ht]
  calc
    _ ≤ norm τ e*norm τ (a*e) := norm_trace_mul τ hτ _ _
    _ ≤ norm τ e*(‖a‖*norm τ e) :=
      mul_le_mul_of_nonneg_left (norm_mul_left τ a e) (norm_nonneg τ e)
    _ = (norm τ e)^2*‖a‖ := by ring
    _ = (τ e).re*‖a‖ := by rw [norm_projection_sq τ he]

variable {N : ℕ} [NeZero N]

variable (e : ZMod N → A) (he : ∀ i,IsStarProjection (e i))
  (ho : ∀ i j,i≠j → e i*e j=0)

omit [PartialOrder A] [StarOrderedRing A] in
include he ho in
lemma phaseElement_corner (m : ZMod N) :
    star (phaseElement e m)*phaseElement e m=∑ j,e j ∧
      phaseElement e m*star (phaseElement e m)=∑ j,e j ∧
      phaseElement e m*(∑ j,e j)=phaseElement e m ∧
      (∑ j,e j)*phaseElement e m=phaseElement e m := by
  obtain ⟨h1,h2⟩ := diagonal_unitary e he ho (fun j => ZMod.stdAddChar (j*m))
    (fun _ => AddChar.norm_apply _ _)
  exact ⟨h1,h2,diagonal_support e he ho _⟩

omit [StarOrderedRing A] in
include he ho in
lemma phaseElement_power_trace (m : ZMod N) (k : ℕ) (hk : 0<k) (a : A) :
    τ (phaseElement e m^k*a)=phaseSum (fun j => τ (e j*a)) ((k:ZMod N)*m) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  rw [phaseElement,diagonal_pow_succ e he ho]
  simp only [diagonal,Finset.sum_mul,smul_mul_assoc,map_sum,map_smul,smul_eq_mul,phaseSum]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  rw [←AddChar.map_nsmul_eq_pow,nsmul_eq_mul]
  congr 1
  ring

include hτ he ho in
lemma phaseElement_mean_bound [Fact N.Prime] (q : A) (hq : IsStarProjection q)
    (hpart : ∑ j,e j=q) (ht : ∀ i,(τ (e i)).re=(τ q).re/(N:ℝ))
    (a : A) (k : ℕ) (hk : 0<k) (hkN : k<N) :
    (∑ m : ZMod N, ‖τ (phaseElement e m^k*a)‖^2) ≤ (τ q).re^2*‖a‖^2 := by
  rcases hpart with rfl
  have hkz : (k:ZMod N)≠0 := by
    intro hz
    have hh := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt hkN,ZMod.val_zero] at hh
    omega
  simp only [phaseElement_power_trace τ e he ho _ k hk a]
  rw [phase_parseval_mul _ _ hkz]
  have htq : 0 ≤ (τ (∑ index,e index)).re := (τ.map_nonneg hq.nonneg).1
  have hN : 0<(N:ℝ) := Nat.cast_pos.mpr (NeZero.pos N)
  calc
    _ ≤ (N:ℝ)*∑ _i : ZMod N, ((τ (∑ index,e index)).re/(N:ℝ)*‖a‖)^2 := by
      apply mul_le_mul_of_nonneg_left _ hN.le
      apply Finset.sum_le_sum
      intro i _
      apply (sq_le_sq₀ (_root_.norm_nonneg _) (by positivity)).mpr
      simpa only [ht] using trace_projection_mul_le τ hτ (e i) a (he i)
    _ = (τ (∑ index,e index)).re^2*‖a‖^2 := by
      simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]
      field_simp

include hτ he ho in
theorem exists_phase_finite {J : Type*} [Fintype J] [Fact N.Prime]
    (q : A) (hq : IsStarProjection q) (hpart : ∑ j,e j=q)
    (ht : ∀ i,(τ (e i)).re=(τ q).re/(N:ℝ)) (hqt : 0<(τ q).re)
    (a : J → A) (k : J → ℕ) (hk : ∀ j,0<k j ∧ k j<N)
    {ε : ℝ} (hε : 0<ε) (hbudget : (∑ j,‖a j‖^2)<(N:ℝ)*ε^2) :
    ∃ u : A, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
      (∀ j,‖τ (u^k j*a j)‖<ε*(τ q).re) ∧
      (∀ S : StarSubalgebra ℂ A, (∀ i,e i∈S) → u∈S) := by
  classical
  have hsum : (∑ m : ZMod N, ∑ j,‖τ (phaseElement e m^k j*a j)‖^2)<
      ∑ _m : ZMod N,(ε*(τ q).re)^2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ j,(τ q).re^2*‖a j‖^2 :=
        Finset.sum_le_sum (fun j _ => phaseElement_mean_bound τ hτ e he ho q hq hpart ht
          (a j) (k j) (hk j).1 (hk j).2)
      _ = (τ q).re^2*(∑ j,‖a j‖^2) := (Finset.mul_sum _ _ _).symm
      _ < (τ q).re^2*((N:ℝ)*ε^2) := mul_lt_mul_of_pos_left hbudget (sq_pos_of_pos hqt)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,ZMod.card,nsmul_eq_mul]; ring
  obtain ⟨m,_,hm⟩ := Finset.exists_lt_of_sum_lt hsum
  obtain ⟨hu1,hu2,hu3,hu4⟩ := phaseElement_corner e he ho m
  rw [hpart] at hu1 hu2 hu3 hu4
  refine ⟨phaseElement e m,hu1,hu2,hu3,hu4,?_,?_,?_⟩
  · have hn : ‖phaseElement e m‖^2=‖q‖ := by
      rw [←hu1,CStarRing.norm_star_mul_self,pow_two]
    have hqnorm := hq.norm_le q
    nlinarith [_root_.norm_nonneg (phaseElement e m)]
  · intro j
    have hj : ‖τ (phaseElement e m^k j*a j)‖^2 < (ε*(τ q).re)^2 :=
      (Finset.single_le_sum (fun i _ => sq_nonneg ‖τ (phaseElement e m^k i*a i)‖)
        (Finset.mem_univ j)).trans_lt hm
    exact (sq_lt_sq₀ (_root_.norm_nonneg _) (mul_nonneg hε.le hqt.le)).mp hj
  · intro S hS
    exact S.sum_mem (fun i _ => S.smul_mem (hS i) _)

end Trace

end Kadison.CornerPhase

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_RelativeCornerPhase
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.UnitaryDualAction.action
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder BigOperators InnerProductSpace

namespace Kadison.CornerPhase

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable (M N : VonNeumannAlgebra H) (hNM : N ≤ M)

variable (τ : M →ₚ[ℂ] ℂ) (hτ : ∀ a b : M, τ (a*b)=τ (b*a))

include hτ hNM in
theorem exists_relative_corner_phase_oai {J : Type*} [Fintype J]
    (hnormal : NormalGNS.BoundedWOTContinuous M τ)
    (hfaith : ∀ a : M,τ (star a*a)=0 → a=0)
    (hN : DiffuseProjection.HasNoMinimalProjections N)
    (q : M) (hq : IsStarProjection q) (hqN : (q : H →L[ℂ] H)∈N)
    (hqt : 0<(τ q).re)
    (a : J → M) (k : J → ℕ) (hk : ∀ j,0<k j) {ε : ℝ} (hε : 0<ε) :
    ∃ u : M, star u*u=q ∧ u*star u=q ∧ u*q=u ∧ q*u=u ∧ ‖u‖ ≤ 1 ∧
      (∀ j, ‖τ (u^k j*a j)‖<ε*(τ q).re) ∧ (u : H →L[ℂ] H)∈N := by
  classical
  obtain ⟨L,hL⟩ := exists_nat_gt ((∑ j,‖a j‖^2)/ε^2)
  obtain ⟨n,hn,hprime⟩ := Nat.exists_infinite_primes (max L (1+Finset.univ.sup k))
  have hLn : L ≤ n := (le_max_left _ _).trans hn
  have hkn (j : J) : k j<n := by
    have hj := Finset.le_sup (s:=Finset.univ) (f:=k) (Finset.mem_univ j)
    have hh : 1+Finset.univ.sup k ≤ n := (le_max_right _ _).trans hn
    omega
  let : Fact n.Prime := ⟨hprime⟩
  let : NeZero n := ⟨hprime.ne_zero⟩
  have hnpos : 0<(n:ℝ) := Nat.cast_pos.mpr hprime.pos
  have hbudget : (∑ j,‖a j‖^2)<(n:ℝ)*ε^2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hε)).mp
    exact hL.trans_le (by exact_mod_cast hLn)
  let ι := NormalSubalgebra.inclusion M N hNM
  let σ := NormalSubalgebra.trace M N hNM τ
  let qN : N := ⟨q,hqN⟩
  have hqNproj : IsStarProjection qN := by
    constructor
    · exact Subtype.ext (congrArg (fun a : M => (a : H →L[ℂ] H)) hq.isIdempotentElem.eq)
    · exact Subtype.ext (congrArg (fun a : M => (a : H →L[ℂ] H)) hq.isSelfAdjoint.star_eq)
  obtain ⟨p,hp,ho,hsum⟩ := NormalGNS.exists_projection_partition N σ
    (NormalSubalgebra.tracial M N hNM τ hτ)
    (NormalSubalgebra.normal M N hNM τ hnormal)
    (NormalSubalgebra.faithful M N hNM τ hfaith) hN
    n qN hqNproj (t:=(τ q).re/n) (by positivity) (by change (τ q).re=_; field_simp)
  let e : ZMod n → M := fun i => ι (p ((ZMod.finEquiv n).symm i))
  have he : ∀ i,IsStarProjection (e i) := fun i => (hp _).1.map ι
  have heo : ∀ i j,i≠j → e i*e j=0 := by
    intro i j hij
    change ι (p _)*ι (p _)=0
    rw [←map_mul,ho _ _ (fun hh => hij ((ZMod.finEquiv n).symm.injective hh)),map_zero]
  have hep : ∑ i,e i=q := by
    change ∑ i,ι (p ((ZMod.finEquiv n).symm i))=ι qN
    rw [←map_sum,←hsum]
    congr 1
    exact Fintype.sum_equiv (ZMod.finEquiv n).symm.toEquiv _ _ (fun _ => rfl)
  obtain ⟨u,h1,h2,h3,h4,h5,h6,hmem⟩ := exists_phase_finite τ hτ e he heo q hq hep
    (fun _ => (hp _).2.2) hqt a k (fun j => ⟨hk j,hkn j⟩) hε hbudget
  refine ⟨u,h1,h2,h3,h4,h5,h6,?_⟩
  exact hmem (N.toStarSubalgebra.comap M.toStarSubalgebra.subtype)
    (fun i => (p _).property)

end Kadison.CornerPhase

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.CornerPhase.exists_relative_corner_phase_oai.{u_1, u_2} := @OAI.Kadison.CornerPhase.exists_relative_corner_phase_oai.{u_1, u_2}
