-- Prove2me | solution 1 for OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-26T15:56:29.731277+00:00
-- url     : https://prove2.me/submissions/16340fcb-c6fe-480a-aff8-7044e595c8d5

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_KaplanskyStableFiniteness
import Definitions.Def_OAIQ15Sf012
import Theorems.Thm_OAI_KaplanskyConsequences_QuasiValue_ultra_polar_corner

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_PartialIsometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]

namespace IsPartialIsometry
variable {v w : A}
lemma star_op (hv : IsPartialIsometry v) : IsPartialIsometry (star v) := by
  have h := congrArg Star.star hv
  simpa only [IsPartialIsometry,star_mul,star_star,mul_assoc] using h
lemma initial (hv : IsPartialIsometry v) : IsStarProjection (star v*v) := by
  refine ⟨?_,(star_mul_self_nonneg _).isSelfAdjoint⟩
  change (star v*v)*(star v*v)=star v*v
  calc _ = star v*(v*star v*v) := by noncomm_ring
       _ = _ := by rw [hv]
lemma final (hv : IsPartialIsometry v) : IsStarProjection (v*star v) := by
  simpa only [star_star] using hv.star_op.initial
lemma norm_le (hv : IsPartialIsometry v) : ‖v‖ ≤ 1 := by
  have h := hv.initial.norm_le
  rw [CStarRing.norm_star_mul_self] at h
  nlinarith [norm_nonneg v]
lemma of_initial (h : IsStarProjection (star v*v)) : IsPartialIsometry v := by
  have hz : star (v*star v*v-v)*(v*star v*v-v)=0 := by
    simp only [star_sub,star_mul,star_star]
    calc
      _ = (star v*v)*(star v*v)*(star v*v)-(star v*v)*(star v*v)-
        (star v*v)*(star v*v)+star v*v := by noncomm_ring
      _ = 0 := by simp only [h.isIdempotentElem.eq,sub_self,zero_sub,neg_add_cancel]
  exact sub_eq_zero.mp ((CStarRing.star_mul_self_eq_zero_iff _).mp hz)
lemma mul_initial (hv : IsPartialIsometry v) : v*(star v*v)=v := by
  simpa only [IsPartialIsometry,mul_assoc] using hv
lemma final_mul (hv : IsPartialIsometry v) : (v*star v)*v=v := hv
lemma mul_initial_compl (hv : IsPartialIsometry v) : v*(1-star v*v)=0 := by
  rw [mul_sub,mul_one,hv.mul_initial,sub_self]
lemma final_compl_mul (hv : IsPartialIsometry v) : (1-v*star v)*v=0 := by
  rw [sub_mul,one_mul,hv.final_mul,sub_self]
lemma initial_compl_mul_star (hv : IsPartialIsometry v) : (1-star v*v)*star v=0 := by
  simpa only [star_mul,star_sub,star_one,star_star,star_zero,mul_assoc] using congrArg Star.star hv.mul_initial_compl
lemma star_mul_final_compl (hv : IsPartialIsometry v) : star v*(1-v*star v)=0 := by
  simpa only [star_mul,star_sub,star_one,star_star,star_zero] using congrArg Star.star hv.final_compl_mul

lemma add_orthogonal (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (hvw : star v*w=0) (hvw' : v*star w=0) : IsPartialIsometry (v+w) := by
  have hwv : star w*v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg Star.star hvw
  have hwv' : w*star v=0 := by simpa only [star_mul,star_star,star_zero] using congrArg Star.star hvw'
  change (v+w)*star (v+w)*(v+w)=v+w
  simp only [star_add,add_mul,mul_add,hvw',hwv',zero_add,add_zero]
  simp only [mul_assoc,hvw,hwv,mul_zero,zero_add,add_zero,
    hv.mul_initial,hw.mul_initial]

lemma initial_of_factor {x : A} (hv : IsPartialIsometry v)
    (hf : v*CFC.sqrt (star x*x)=x) : (star v*v)*CFC.sqrt (star x*x)=CFC.sqrt (star x*x) := by
  let b := CFC.sqrt (star x*x)
  have hb : IsSelfAdjoint b := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hbb : b*b=star x*x := CFC.sqrt_mul_sqrt_self _ (star_mul_self_nonneg x)
  have he : b*(star v*v)*b=b*b := by
    calc _ = star (v*b)*(v*b) := by rw [star_mul,hb.star_eq]; noncomm_ring
         _ = star x*x := by rw [hf]
         _ = _ := hbb.symm
  have hz : star ((1-star v*v)*b)*((1-star v*v)*b)=0 := by
    rw [star_mul,hv.initial.one_sub.isSelfAdjoint.star_eq,hb.star_eq]
    calc _ = b*((1-star v*v)*(1-star v*v))*b := by noncomm_ring
         _ = b*(1-star v*v)*b := by rw [hv.initial.one_sub.isIdempotentElem.eq]
         _ = b*b-b*(star v*v)*b := by noncomm_ring
         _ = 0 := by rw [he,sub_self]
  have hh := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [sub_mul,one_mul] at hh
  exact (sub_eq_zero.mp hh).symm
end IsPartialIsometry

end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiValue
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
open scoped ComplexOrder
open Kaplansky SpectralKernel
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

namespace QuasiValue
variable {A : Type*} [CStarAlgebra A]

variable (V : QuasiValue A)

lemma q_nonneg (x : A) : 0≤V.q x := V.nonneg (star_mul_self_nonneg x)
lemma q_bound (x : A) : V.q x≤‖x‖^2 := by
  simpa only [q,CStarRing.norm_star_mul_self,pow_two] using
    (le_abs_self (V.val (star x*x))).trans (V.bound _)

lemma val_scalar_sub {x : A} (hx : IsSelfAdjoint x) (r : ℝ) :
    V.val (r • 1-x)=r-V.val x := by
  have hn := V.smul (-1) x
  simp only [neg_one_smul,neg_mul,one_mul] at hn
  rw [sub_eq_add_neg,V.add_commute ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one A)) hx.neg
      (by change (r • (1:A)) * (-x)=(-x)*(r • (1:A)); simp),V.smul,V.one,hn]
  ring

lemma val_shift {x : A} (hx : IsSelfAdjoint x) (r : ℝ) :
    V.val (x+r • 1)=V.val x+r := by
  rw [V.add_commute hx ((IsSelfAdjoint.all r).smul (IsSelfAdjoint.one A))
    (by change x*(r • (1:A))=(r • (1:A))*x; simp),V.smul,V.one,mul_one]

end QuasiValue
end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiNull
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma null_of_val_zero {a : A} (ha : 0 ≤ a) (hx : V.val a = 0) :
    IsNull V a := by
  have hs : IsNull V (CFC.sqrt a) := by
    simpa only [IsNull,(CFC.sqrt_nonneg a).isSelfAdjoint.star_eq,
      CFC.sqrt_mul_sqrt_self a ha] using hx
  simpa only [CFC.sqrt_mul_sqrt_self a ha] using null_mul_left V hs (CFC.sqrt a)


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_QuasiFinite
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma finite_mod_null (x : A)
    (hx : IsNull V (star x*x-1)) : IsNull V (x*star x-1) := by
  let : Nontrivial A := nontrivial_of_ne (1:A) 0 (fun h =>
    zero_ne_one (V.zero.symm.trans ((congrArg V.val h.symm).trans V.one)))
  let I := nullIdeal V
  let q := I.mkStarAlgHom
  have hsmul (r : ℝ) (a : A) : q (r • a) = r • q a :=
    q.toAlgHom.map_smul_of_tower r a
  have qzero (a : A) : q a = 0 ↔ IsNull V a := I.mk_eq_zero a
  have hiso : star (q x)*q x = 1 := by
    have h := (qzero _).2 hx
    simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using h
  have hp : IsStarProjection (q x*star (q x)) := by
    refine ⟨?_, (mul_star_self_nonneg _).isSelfAdjoint⟩
    change (q x*star (q x))*(q x*star (q x))=q x*star (q x)
    calc _ = q x*(star (q x)*q x)*star (q x) := by noncomm_ring
         _ = _ := by rw [hiso,mul_one]
  let w := 1-q x*star (q x)
  have hw : 0 ≤ w := hp.one_sub.nonneg
  obtain ⟨y, hy⟩ := I.mk_surjective (CFC.sqrt w)
  change q y = CFC.sqrt w at hy
  let u := star y*y
  have hu : 0 ≤ u := star_mul_self_nonneg y
  have hqu : q u = w := by
    simp only [u,map_mul,map_star,hy,(CFC.sqrt_nonneg w).isSelfAdjoint.star_eq]
    exact CFC.sqrt_mul_sqrt_self w hw
  let c := ‖x*star x‖+1
  have hc : 0 ≤ c-1 := by dsimp [c]; linarith [norm_nonneg (x*star x)]
  have ha : 0 ≤ c • (1 : A)-x*star x := by
    apply sub_nonneg.mpr
    have ht := (mul_star_self_nonneg x).isSelfAdjoint.le_algebraMap_norm_self
    rw [Algebra.algebraMap_eq_smul_one] at ht
    exact ht.trans (smul_le_smul_of_nonneg_right (by dsimp [c]; linarith) zero_le_one)
  have hb : 0 ≤ u + (c-1) • (1 : A) := add_nonneg hu (smul_nonneg hc zero_le_one)
  have hab : IsNull V ((c • (1 : A)-x*star x) - (u+(c-1) • 1)) := by
    apply (qzero _).1
    simp only [map_sub,map_add,map_mul,map_star,map_one,hsmul,hqu]
    dsimp [w]
    rw [sub_smul,one_smul]
    abel
  have hvx : V.val (x*star x) = 1 := by
    rw [V.square_swap]
    exact (val_eq_of_null_sub V (star_mul_self_nonneg x) zero_le_one hx).trans V.one
  have hv := val_eq_of_null_sub V ha hb hab
  rw [V.val_scalar_sub (mul_star_self_nonneg x).isSelfAdjoint,
    V.val_shift hu.isSelfAdjoint (c-1),hvx] at hv
  have hvu : V.val u = 0 := by linarith
  have hnull := null_of_val_zero V hu hvu
  have hqu0 := (qzero _).2 hnull
  have hw0 : w=0 := hqu.symm.trans hqu0
  apply (qzero _).1
  simp only [map_sub,map_mul,map_star,map_one]
  exact sub_eq_zero.mpr (sub_eq_zero.mp hw0).symm

lemma faithfulQuotient_finite (x : V.FaithfulQuotient) (hx : star x*x=1) : x*star x=1 := by
  obtain ⟨a,ha⟩ := V.nullIdeal.mk_surjective x
  change V.quotientHom a=x at ha
  subst x
  have hn : V.IsNull (star a*a-1) := by
    apply (V.nullIdeal.mk_eq_zero _).mp
    change V.quotientHom (star a*a-1)=0
    simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using hx
  have hh := (V.nullIdeal.mk_eq_zero _).mpr (V.finite_mod_null a hn)
  change V.quotientHom (a*star a-1)=0 at hh
  simpa only [map_sub,map_mul,map_star,map_one,sub_eq_zero] using hh


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Quotient
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open scoped ComplexOrder
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] (V : QuasiValue A)

lemma quotQ_nonneg (x : V.FaithfulQuotient) : 0≤V.quotQ x := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact V.q_nonneg a

lemma quotQ_eq_zero (x : V.FaithfulQuotient) : V.quotQ x=0 ↔ x=0 := by
  obtain ⟨a,rfl⟩ := V.nullIdeal.mk_surjective x
  exact (V.nullIdeal.mk_eq_zero a).symm

lemma quotQ_bound (x : V.FaithfulQuotient) : V.quotQ x≤‖x‖^2 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let δ := min 1 (ε/(2*‖x‖+1))
  have hδ : 0<δ := lt_min zero_lt_one (div_pos hε (by positivity))
  obtain ⟨a,ha,hn⟩ := V.nullIdeal.norm_mk_lt x hδ
  change V.quotientHom a=x at ha
  have hq := V.q_bound a
  rw [← V.quotQ_map a,ha] at hq
  have hδ1 : δ≤1 := min_le_left ..
  have hd : δ*(2*‖x‖+1)≤ε := by
    exact (le_div_iff₀ (by positivity : 0<2*‖x‖+1)).mp (min_le_right ..)
  nlinarith [norm_nonneg a,norm_nonneg x]

lemma quotQ_projection_lift {a : A} (ha : 0≤a) (hp : IsStarProjection (V.quotientHom a)) :
    V.quotQ (V.quotientHom a)=V.val a := by
  change V.val (star a*a)=V.val a
  apply V.val_eq_of_null_sub (star_mul_self_nonneg a) ha
  apply (V.nullIdeal.mk_eq_zero _).mp
  change V.quotientHom (star a*a-a)=0
  simp only [map_sub,map_mul,map_star,hp.isSelfAdjoint.star_eq,hp.isIdempotentElem.eq,sub_self]

lemma quotQ_partial_projection {v : V.FaithfulQuotient}
    (hv : IsStarProjection (star v*v)) : V.quotQ (star v*v)=V.quotQ v := by
  obtain ⟨a,ha⟩ := V.nullIdeal.mk_surjective v
  change V.quotientHom a=v at ha
  subst v
  have hp : IsStarProjection (V.quotientHom (star a*a)) := by simpa only [map_mul,map_star] using hv
  have h := V.quotQ_projection_lift (star_mul_self_nonneg a) hp
  simpa only [map_mul,map_star,quotQ_map,q] using h

lemma projection_add {B : Type*} [CStarAlgebra B] {p q : B}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p*q=0) : IsStarProjection (p+q) := by
  have hqp : q*p=0 := by simpa only [star_mul,hp.isSelfAdjoint.star_eq,hq.isSelfAdjoint.star_eq,star_zero] using congrArg star hpq
  refine ⟨?_,hp.isSelfAdjoint.add hq.isSelfAdjoint⟩
  change (p+q)*(p+q)=p+q
  simp only [add_mul,mul_add,hp.isIdempotentElem.eq,hq.isIdempotentElem.eq,hpq,hqp,add_zero,zero_add]

lemma selfAdjoint_lift (x : V.FaithfulQuotient) (hx : IsSelfAdjoint x) :
    ∃ a : A, IsSelfAdjoint a ∧ V.quotientHom a=x := by
  obtain ⟨b,hb⟩ := V.nullIdeal.mk_surjective x
  change V.quotientHom b=x at hb
  refine ⟨(2:ℝ)⁻¹ • (b+star b),?_,?_⟩
  · change star ((2:ℝ)⁻¹ • (b+star b))=(2:ℝ)⁻¹ • (b+star b)
    simp only [star_smul,star_trivial,star_add,star_star,add_comm]
  · have hs : V.quotientHom ((2:ℝ)⁻¹ • (b+star b)) = (2:ℝ)⁻¹ • V.quotientHom (b+star b) :=
      V.quotientHom.toAlgHom.map_smul_of_tower _ _
    rw [hs,map_add,map_star,hb,hx.star_eq,← two_smul ℝ x,smul_smul]
    norm_num

open scoped CStarAlgebra in
lemma quotQ_projection_add [Nontrivial A] {p q : V.FaithfulQuotient}
    (hp : IsStarProjection p) (hq : IsStarProjection q) (hpq : p*q=0) :
    V.quotQ (p+q)=V.quotQ p+V.quotQ q := by
  obtain ⟨a,ha,he⟩ := V.selfAdjoint_lift (p-q) (hp.isSelfAdjoint.sub hq.isSelfAdjoint)
  have hph := CFC.posPart_negPart_unique (a:=p-q) rfl hpq hp.nonneg hq.nonneg
  have hmapP : V.quotientHom a⁺=p := by
    rw [CFC.posPart_def,NonUnitalStarAlgHomClass.map_cfcₙ V.quotientHom (fun t : ℝ => t⁺) a (ha:=ha) (hφa:=ha.map V.quotientHom),← CFC.posPart_def,he,hph.1]
  have hmapN : V.quotientHom a⁻=q := by
    rw [CFC.negPart_def,NonUnitalStarAlgHomClass.map_cfcₙ V.quotientHom (fun t : ℝ => t⁻) a (ha:=ha) (hφa:=ha.map V.quotientHom),← CFC.negPart_def,he,hph.2]
  have hP : IsStarProjection (V.quotientHom a⁺) := hmapP ▸ hp
  have hN : IsStarProjection (V.quotientHom a⁻) := hmapN ▸ hq
  have hPN : IsStarProjection (V.quotientHom (a⁺+a⁻)) := by
    rw [map_add,hmapP,hmapN]; exact projection_add hp hq hpq
  have hval := V.add_commute (CFC.posPart_nonneg a).isSelfAdjoint (CFC.negPart_nonneg a).isSelfAdjoint
    (show Commute a⁺ a⁻ from (CFC.posPart_mul_negPart a).trans (CFC.negPart_mul_posPart a).symm)
  rw [← V.quotQ_projection_lift (CFC.posPart_nonneg a) hP,
    ← V.quotQ_projection_lift (CFC.negPart_nonneg a) hN,
    ← V.quotQ_projection_lift (add_nonneg (CFC.posPart_nonneg a) (CFC.negPart_nonneg a)) hPN,
    map_add,hmapP,hmapN] at hval
  exact hval


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_UltraDiagonal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology

lemma ultra_selector (u : Ultrafilter ℕ) (hu : (u : Filter ℕ)≤atTop)
    (s : ℕ → Set ℕ) (hs : ∀ n, s n ∈ u) :
    ∃ k : ℕ → ℕ, Tendsto k u atTop ∧ ∀ i, k i≠0 → ∀ j≤k i, i∈s j := by
  classical
  let P (i n : ℕ) := ∀ j≤n, i∈s j
  have he (n : ℕ) : ∀ᶠ i in (u : Filter ℕ), P i n := by
    induction n with
    | zero => simpa [P] using hs 0
    | succ n ih =>
      filter_upwards [ih,hs (n+1)] with i hi hin
      intro j hj
      rcases (Nat.le_succ_iff.mp hj) with hj | hj
      · exact hi j hj
      · simpa only [hj] using hin
  let k (i : ℕ) := Nat.findGreatest (P i) i
  refine ⟨k,?_,?_⟩
  · apply tendsto_atTop.2
    intro n
    filter_upwards [he n,hu (eventually_ge_atTop n)] with i hi hin
    exact Nat.le_findGreatest hin hi
  · intro i hi
    exact (Nat.findGreatest_eq_iff.mp (rfl : Nat.findGreatest (P i) i=k i)).2.1 hi


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_UltraSaturation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue
open Filter Topology
open scoped ComplexOrder ENNReal

namespace StarTerm
variable {C D E : Type*}
lemma map_eval [Ring D] [StarRing D] [Ring E] [StarRing E]
    {F : Type*} [FunLike F D E] [NonUnitalRingHomClass F D E] [StarHomClass F D E]
    (φ : F) (c : C → D) (x : D) (p : StarTerm C) :
    φ (p.eval c x)=p.eval (fun a => φ (c a)) (φ x) := by
  induction p <;> simp_all [eval,map_star]
end StarTerm

variable {A : Type*} [CStarAlgebra A] [Nontrivial A]

variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

lemma ultra_q_tendsto (a : Sequences (A:=A) (ι:=ℕ)) :
    Tendsto (fun i => V.q (a i)) u (𝓝 (V.ultraQ u (V.ultraHom u a))) :=
  V.ultra_val_tendsto u (star a*a)

include hu in

lemma ultra_realize {ι : Type*} [Fintype ι] (P : ι → StarTerm (V.UltraQuotient u)) (t : ι → ℝ)
    (h : ∀ ε : ℝ, 0 < ε → ∃ x : V.UltraQuotient u,
      ‖x‖ ≤ 1 ∧ ∀ j, |V.ultraQ u ((P j).eval id x)-t j| < ε) :
    ∃ x : V.UltraQuotient u, ∀ j, V.ultraQ u ((P j).eval id x)=t j := by
  classical
  let W := V.ultra u
  let Q := V.ultraHom u
  have lift (x : V.UltraQuotient u) : ∃ a : Sequences (A:=A) (ι:=ℕ), Q a=x := W.nullIdeal.mk_surjective x
  choose c hc using lift
  let ε (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  choose x hx hxt using fun n => h (ε n/2) (half_pos (hε n))
  have liftn (n : ℕ) : ∃ a : Sequences (A:=A) (ι:=ℕ), Q a=x n ∧ ‖a‖ < 2 := by
    obtain ⟨a,ha,hn⟩ := W.nullIdeal.norm_mk_lt (x n) zero_lt_one
    exact ⟨a,ha,hn.trans_le (by linarith [hx n])⟩
  choose a ha han using liftn
  let F (j : ι) (i : ℕ) (b : A) : ℝ := V.q ((P j).eval (fun d => c d i) b)-t j
  have ht (n : ℕ) (j : ι) :
      Tendsto (fun i => F j i (a n i)) u (𝓝 (V.ultraQ u ((P j).eval id (x n))-t j)) := by
    have he' : Q ((P j).eval c (a n))=(P j).eval id (x n) := by
      rw [StarTerm.map_eval Q,ha n]
      congr 2
      funext d
      exact hc d
    have heval (i : ℕ) : ((P j).eval c (a n)) i=(P j).eval (fun d => c d i) (a n i) := by
      have he := StarTerm.map_eval (seqEvalHom (A:=A) i) c (a n) (P j)
      simp only [seqEvalHom] at he
      exact he
    dsimp only [Q] at he'
    have hh := (V.ultra_q_tendsto u ((P j).eval c (a n))).sub_const (t j)
    simpa only [he',heval] using hh
  let s (n : ℕ) := {i | ∀ j, |F j i (a n i)| ≤ ε n}
  have hs (n : ℕ) : s n ∈ u := by
    have hj (j : ι) : ∀ᶠ i in (u : Filter ℕ), |F j i (a n i)| ≤ ε n := by
      have hlt : |V.ultraQ u ((P j).eval id (x n))-t j| < ε n := (hxt n j).trans (by linarith [hε n])
      exact ((ht n j).abs.eventually (eventually_lt_nhds hlt)).mono (fun _ h => h.le)
    exact Filter.eventually_all.mpr hj
  obtain ⟨k,hk,hgood⟩ := ultra_selector u hu s hs
  let b : Sequences (A:=A) (ι:=ℕ) := ⟨fun i => a (k i) i,memℓp_infty
    ⟨2,by rintro _ ⟨i,rfl⟩; exact (lp.norm_apply_le_norm ENNReal.top_ne_zero (a (k i)) i).trans (han (k i)).le⟩⟩
  refine ⟨Q b,?_⟩
  intro j
  have hb : Tendsto (fun i => F j i (b i)) u (𝓝 0) := by
    have hbound : ∀ᶠ i in (u : Filter ℕ), |F j i (b i)| ≤ ε (k i) := by
      filter_upwards [hk (eventually_ge_atTop 1)] with i hi
      exact hgood i (Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hi)) (k i) le_rfl j
    apply squeeze_zero_norm' _ ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)).comp hk)
    simpa only [Real.norm_eq_abs,Function.comp_apply] using hbound
  have hqb : Q ((P j).eval c b)=(P j).eval id (Q b) := by
    rw [StarTerm.map_eval Q]
    congr 2
    funext d
    exact hc d
  have heval (i : ℕ) : ((P j).eval c b) i=(P j).eval (fun d => c d i) (b i) := by
    exact StarTerm.map_eval (seqEvalHom (A:=A) i) c b (P j)
  dsimp only [Q] at hqb
  have ht' := (V.ultra_q_tendsto u ((P j).eval c b)).sub_const (t j)
  have hz : V.ultraQ u ((P j).eval id (Q b))-t j=0 := by
    apply tendsto_nhds_unique _ hb
    simpa only [hqb,heval] using ht'
  exact sub_eq_zero.mp hz

end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Maximal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

include hu in
lemma ultra_maximal_extension {v : V.UltraQuotient u} (hv : IsPartialIsometry v) :
    ∃ w : V.UltraQuotient u, IsPartialIsometry w ∧ w*(star v*v)=v ∧
      ∀ z : V.UltraQuotient u, IsPartialIsometry z → z*(star v*v)=v →
        V.ultraQ u z ≤ V.ultraQ u w := by
  let W := V.ultra u
  let s : Set ℝ := {r | ∃ z : V.UltraQuotient u, IsPartialIsometry z ∧ z*(star v*v)=v ∧ V.ultraQ u z=r}
  have hs : s.Nonempty := ⟨V.ultraQ u v,v,hv,hv.mul_initial,rfl⟩
  have hb : BddAbove s := by
    refine ⟨1,?_⟩
    rintro r ⟨z,hz,_,rfl⟩
    have hn := hz.norm_le
    have hq := W.quotQ_bound z
    nlinarith [norm_nonneg z]
  let S := sSup s
  let t : StarTerm (V.UltraQuotient u) := .var
  let sub (a b : StarTerm (V.UltraQuotient u)) := StarTerm.add a (.neg b)
  let P : Fin 3 → StarTerm (V.UltraQuotient u) :=
    ![sub (.mul (.mul t (.star t)) t) t,
      sub (.mul t (.const (star v*v))) (.const v),t]
  let R : Fin 3 → ℝ := ![0,0,S]
  have happ (ε : ℝ) (hε : 0<ε) : ∃ z : V.UltraQuotient u,
      ‖z‖ ≤ 1 ∧ ∀ j : Fin 3, |V.ultraQ u ((P j).eval id z)-R j| < ε := by
    obtain ⟨r,hr,hlt⟩ := exists_lt_of_lt_csSup hs (sub_lt_self S hε)
    obtain ⟨z,hz,hzv,rfl⟩ := hr
    have hle : V.ultraQ u z≤S := le_csSup hb ⟨z,hz,hzv,rfl⟩
    refine ⟨z,hz.norm_le,?_⟩
    intro j
    fin_cases j <;> simp [P,R,sub,t,StarTerm.eval,← sub_eq_add_neg]
    · change |W.quotQ (z*star z*z-z)| < ε
      rw [show z*star z*z=z from hz,sub_self,W.quotQ_zero,abs_zero]
      exact hε
    · change |W.quotQ (z*(star v*v)-v)| < ε
      rw [hzv,sub_self,W.quotQ_zero,abs_zero]
      exact hε
    · rw [abs_of_nonpos (sub_nonpos.mpr hle)]
      linarith
  obtain ⟨w,hw⟩ := V.ultra_realize u hu P R happ
  have h0 := hw 0
  have h1 := hw 1
  have h2 := hw 2
  simp [P,R,sub,t,StarTerm.eval,← sub_eq_add_neg] at h0 h1 h2
  have hw0 : IsPartialIsometry w := sub_eq_zero.mp ((W.quotQ_eq_zero _).mp h0)
  have hw1 : w*(star v*v)=v := sub_eq_zero.mp ((W.quotQ_eq_zero _).mp h1)
  refine ⟨w,hw0,hw1,?_⟩
  intro z hz hzv
  rw [h2]
  exact le_csSup hb ⟨z,hz,hzv,rfl⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_PartialCorners
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A]
namespace IsPartialIsometry
variable {v w z : A}
lemma extension_initial (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (h : w*(star v*v)=v) : (star w*w)*(star v*v)=star v*v := by
  let p := star v*v
  let q := star w*w
  have hp : IsStarProjection p := hv.initial
  have hq : IsStarProjection q := hw.initial
  have hh : p*q*p=p := by
    calc _ = star (w*p)*(w*p) := by rw [star_mul,hp.isSelfAdjoint.star_eq]; dsimp [q]; noncomm_ring
         _ = _ := by rw [h]
  have hz : star ((1-q)*p)*((1-q)*p)=0 := by
    rw [star_mul,hp.isSelfAdjoint.star_eq,hq.one_sub.isSelfAdjoint.star_eq]
    calc _ = p*((1-q)*(1-q))*p := by noncomm_ring
         _ = p*(1-q)*p := by rw [hq.one_sub.isIdempotentElem.eq]
         _ = p*p-p*q*p := by noncomm_ring
         _ = 0 := by rw [hp.isIdempotentElem.eq,hh,sub_self]
  have he := (CStarRing.star_mul_self_eq_zero_iff _).mp hz
  rw [sub_mul,one_mul] at he
  exact (sub_eq_zero.mp he).symm

lemma orthogonal_of_corners (hw : IsPartialIsometry w)
    (hl : (1-w*star w)*z=z) (hr : z*(1-star w*w)=z) :
    star w*z=0 ∧ w*star z=0 := by
  constructor
  · calc _ = star w*((1-w*star w)*z) := by rw [hl]
         _ = (star w*(1-w*star w))*z := by noncomm_ring
         _ = 0 := by rw [hw.star_mul_final_compl,zero_mul]
  · have hzs : z*star w=0 := by
      calc _ = (z*(1-star w*w))*star w := by rw [hr]
           _ = z*((1-star w*w)*star w) := by noncomm_ring
           _ = 0 := by rw [hw.initial_compl_mul_star,mul_zero]
    simpa only [star_mul,star_star,star_zero] using congrArg Star.star hzs

lemma corner_annihilates_extension (hv : IsPartialIsometry v) (hw : IsPartialIsometry w)
    (h : w*(star v*v)=v) (hr : z*(1-star w*w)=z) : z*(star v*v)=0 := by
  have hi := extension_initial hv hw h
  calc _ = (z*(1-star w*w))*(star v*v) := by rw [hr]
       _ = z*((1-star w*w)*(star v*v)) := by noncomm_ring
       _ = 0 := by rw [sub_mul,one_mul,hi,sub_self,mul_zero]
end IsPartialIsometry

end KaplanskyConsequences

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Polar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
open scoped ComplexOrder ENNReal
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealSMulComm_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealTower_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealCFC_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraNonnegSpectrum_p0
include hu in
lemma ultra_polar (x : V.UltraQuotient u) : ∃ v : V.UltraQuotient u,
    IsPartialIsometry v ∧ v*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hv,hvx,_,_⟩ := V.ultra_polar_corner u hu x 1 1 (IsStarProjection.one _) (mul_one x) (one_mul x)
  exact ⟨v,hv,hvx⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Wandering
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A] (V : QuasiValue A)

lemma quotQ_partial_final {w : V.FaithfulQuotient} (hw : IsPartialIsometry w) :
    V.quotQ (w*star w)=V.quotQ w := by
  simpa only [star_star,V.quotQ_star] using V.quotQ_partial_projection hw.star_op.initial

lemma quotQ_partial_add {w z : V.FaithfulQuotient}
    (hw : IsPartialIsometry w) (hz : IsPartialIsometry z)
    (hwz : star w*z=0) (hwz' : w*star z=0) :
    V.quotQ (w+z)=V.quotQ w+V.quotQ z := by
  have hzw : star z*w=0 := by simpa only [star_mul,star_star,star_zero] using congrArg star hwz
  have ho : (star w*w)*(star z*z)=0 := by
    calc _ = star w*(w*star z)*z := by noncomm_ring
         _ = 0 := by rw [hwz',mul_zero,zero_mul]
  rw [← V.quotQ_partial_projection (hw.add_orthogonal hz hwz hwz').initial]
  have he : star (w+z)*(w+z)=star w*w+star z*z := by
    simp only [star_add,add_mul,mul_add,hwz,hzw,add_zero,zero_add]
  rw [he,V.quotQ_projection_add hw.initial hz.initial ho,
    V.quotQ_partial_projection hw.initial,V.quotQ_partial_projection hz.initial]

lemma unitary_of_residual_corner_zero {w : V.FaithfulQuotient}
    (hw : IsPartialIsometry w)
    (hcorner : ∀ a : V.FaithfulQuotient, (1-w*star w)*a*(1-star w*w)=0) :
    star w*w=1 ∧ w*star w=1 := by
  let p := 1-star w*w
  let q := 1-w*star w
  have hp : IsStarProjection p := hw.initial.one_sub
  have hq : IsStarProjection q := hw.final.one_sub
  have hs (n : ℕ) : ∃ s : V.FaithfulQuotient, IsStarProjection s ∧
      V.quotQ s=(n:ℝ)*V.quotQ p ∧ ∀ a, q*a*s=0 := by
    induction n with
    | zero => exact ⟨0,IsStarProjection.zero _,by simp,by simp⟩
    | succ n ih =>
      obtain ⟨s,hs,hsize,hann⟩ := ih
      let y := star w*s
      have hqS : q*s=0 := by simpa only [mul_one] using hann 1
      have hyi : star y*y=s := by
        simp only [y,star_mul,star_star,hs.isSelfAdjoint.star_eq]
        calc _ = s*(w*star w)*s := by noncomm_ring
             _ = s*s-s*(q*s) := by dsimp [q]; noncomm_ring
             _ = s := by rw [hs.isIdempotentElem.eq,hqS,mul_zero,sub_zero]
      have hy : IsPartialIsometry y := IsPartialIsometry.of_initial (hyi ▸ hs)
      have hyf : y*star y=star w*s*w := by
        simp only [y,star_mul,star_star,hs.isSelfAdjoint.star_eq]
        calc _ = star w*(s*s)*w := by noncomm_ring
             _ = _ := by rw [hs.isIdempotentElem.eq]
      have hr : IsStarProjection (star w*s*w) := hyf ▸ hy.final
      have hor : p*(star w*s*w)=0 := by
        calc _ = (p*star w)*s*w := by noncomm_ring
             _ = 0 := by rw [show p*star w=0 from hw.initial_compl_mul_star,zero_mul,zero_mul]
      refine ⟨p+star w*s*w,projection_add hp hr hor,?_,?_⟩
      · rw [V.quotQ_projection_add hp hr hor,← hyf,V.quotQ_partial_final hy,
          ← V.quotQ_partial_projection hy.initial,hyi,hsize]
        push_cast
        ring
      · intro a
        calc _ = q*a*p+(q*(a*star w)*s)*w := by noncomm_ring
             _ = 0 := by rw [hcorner a,hann (a*star w),zero_mul,add_zero]
  have hb (n : ℕ) : (n:ℝ)*V.quotQ p≤1 := by
    obtain ⟨s,hs,he,_⟩ := hs n
    have hh := V.quotQ_bound s
    have hn := hs.norm_le
    rw [he] at hh
    nlinarith [norm_nonneg s]
  have hz : V.quotQ p=0 := by
    by_contra hn
    have ht : 0<V.quotQ p := lt_of_le_of_ne (V.quotQ_nonneg p) (Ne.symm hn)
    obtain ⟨n,hn⟩ := exists_nat_gt (1/V.quotQ p)
    have hh : 1<(n:ℝ)*V.quotQ p := (div_lt_iff₀ ht).mp hn
    exact (not_lt_of_ge (hb n)) hh
  have hp0 : p=0 := (V.quotQ_eq_zero p).mp hz
  have hi : star w*w=1 := (sub_eq_zero.mp hp0).symm
  exact ⟨hi,V.faithfulQuotient_finite w hi⟩


end KaplanskyConsequences.QuasiValue

end

end OAI
end

section
-- module Solutions.OAIQ15_Sf.Kaplansky_Ultrapower_Unitary
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace KaplanskyConsequences.QuasiValue

open Filter Topology
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing
variable {A : Type*} [CStarAlgebra A] [Nontrivial A]
variable (V : QuasiValue A) (u : Ultrafilter ℕ) (hu : (u : Filter ℕ) ≤ atTop)

include hu in
lemma ultra_unitary_extension {v : V.UltraQuotient u} (hv : IsPartialIsometry v) :
    ∃ w : V.UltraQuotient u, star w*w=1 ∧ w*star w=1 ∧ w*(star v*v)=v := by
  let W := V.ultra u
  obtain ⟨w,hw,hwv,hmax⟩ := V.ultra_maximal_extension u hu hv
  have hcorner (a : V.UltraQuotient u) : (1-w*star w)*a*(1-star w*w)=0 := by
    let p := 1-star w*w
    let q := 1-w*star w
    let b := q*a*p
    have hp : IsStarProjection p := hw.initial.one_sub
    have hq : IsStarProjection q := hw.final.one_sub
    have hbp : b*p=b := by dsimp [b]; rw [mul_assoc,hp.isIdempotentElem.eq]
    have hqb : q*b=b := by dsimp [b]; rw [← mul_assoc,← mul_assoc,hq.isIdempotentElem.eq]
    obtain ⟨z,hz,hzb,hqz,hzp⟩ := V.ultra_polar_corner u hu b p q hp hbp hqb
    obtain ⟨h₁,h₂⟩ := hw.orthogonal_of_corners hqz hzp
    have hzw : IsPartialIsometry (w+z) := hw.add_orthogonal hz h₁ h₂
    have hzv : z*(star v*v)=0 := hv.corner_annihilates_extension hw hwv hzp
    have he : (w+z)*(star v*v)=v := by rw [add_mul,hwv,hzv,add_zero]
    have hsize := hmax (w+z) hzw he
    change W.quotQ (w+z) ≤ W.quotQ w at hsize
    rw [W.quotQ_partial_add hw hz h₁ h₂] at hsize
    have hzero : W.quotQ z=0 := by linarith [W.quotQ_nonneg z]
    have hz0 := (W.quotQ_eq_zero z).mp hzero
    rw [hz0,zero_mul] at hzb
    exact hzb.symm
  obtain ⟨hi,hf⟩ := W.unitary_of_residual_corner_zero hw hcorner
  exact ⟨w,hi,hf,hwv⟩

attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealSMulComm_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealTower_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraRealCFC_p0
attribute [local instance] OAI.KaplanskyConsequences.QuasiValue.ultraNonnegSpectrum_p0
include hu in
lemma ultra_unitary_polar_oai (x : V.UltraQuotient u) :
    ∃ w : V.UltraQuotient u, star w*w=1 ∧ w*star w=1 ∧
      w*CFC.sqrt (star x*x)=x := by
  obtain ⟨v,hv,hvx⟩ := V.ultra_polar u hu x
  obtain ⟨w,hi,hf,hwv⟩ := V.ultra_unitary_extension u hu hv
  refine ⟨w,hi,hf,?_⟩
  calc _ = w*((star v*v)*CFC.sqrt (star x*x)) :=
          (congrArg (fun a : V.UltraQuotient u => w * a) (hv.initial_of_factor hvx)).symm
       _ = (w*(star v*v))*CFC.sqrt (star x*x) := by noncomm_ring
       _ = x := by rw [hwv,hvx]


end KaplanskyConsequences.QuasiValue

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar_oai.{u_1} := @OAI.KaplanskyConsequences.QuasiValue.ultra_unitary_polar_oai.{u_1}
