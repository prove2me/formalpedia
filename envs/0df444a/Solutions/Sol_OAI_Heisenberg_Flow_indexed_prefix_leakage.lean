-- Prove2me | solution 1 for OAI.Heisenberg.Flow.indexed_prefix_leakage
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T08:31:57.05414+00:00
-- url     : https://prove2.me/submissions/955403c0-6d8e-4b74-89e3-5073497a8e29

import Mathlib
import Definitions.Def_Heisenberg
import Definitions.Def_OAIW2HM000
import Definitions.Def_OAIW2HM001

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeDeterminants
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

namespace Heisenberg.LayeredExchange
variable {T V : Type*}

lemma fibers_update [DecidableEq T] (σ : T → Equiv.Perm V) (t : T) (τ : Equiv.Perm V) :
    fibers (Function.update σ t (τ * σ t)) =
      fibers (Function.update (fun _ => 1) t τ) * fibers σ := by
  ext ⟨u,v⟩ <;> by_cases h : u = t <;> simp [fibers,Function.update,h]

lemma fibers_swap [DecidableEq T] [DecidableEq V] (t : T) (u v : V) :
    fibers (Function.update (fun _ : T => 1) t (Equiv.swap u v)) = Equiv.swap (t,u) (t,v) := by
  ext ⟨a,b⟩ <;> by_cases ht : a = t
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]
  · subst a
    simp [fibers,Equiv.swap_apply_def]
    split_ifs <;> simp_all
  · simp [fibers,Function.update,ht,Equiv.swap_apply_def]

end Heisenberg.LayeredExchange

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExchangeCycles
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix

open scoped Classical
namespace Heisenberg.Cycle

section
open Equiv
variable {V : Type*}

variable [Fintype V]

 theorem card_colorSpace (π : Perm V) (P : Set V) :
    Nat.card (colorSpace π P) = 2 ^ missingCount π P := by
  let := Fintype.ofFinite (MissingClasses π P)
  rw [Nat.card_congr (colorEquiv π P),Nat.card_fun]
  simp [missingCount]

lemma finrank_comparison {K W : Type*} [Field K] [AddCommGroup W] [Module K W]
    [FiniteDimensional K W] (A B : Submodule K W) (f : W →ₗ[K] K)
    (h : ∀ x ∈ A, f x = 0 → x ∈ B) :
    Module.finrank K A ≤ Module.finrank K B + 1 := by
  let g : A →ₗ[K] K := f.comp A.subtype
  let k : LinearMap.ker g →ₗ[K] B :=
    { toFun := fun x => ⟨x.val.val,h x.val.val x.val.property x.property⟩
      map_add' := by intro x y; rfl
      map_smul' := by intro r x; rfl }
  have hk : Function.Injective k := by
    intro x y he
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : B => z.val) he
  have hd := k.finrank_le_finrank_of_injective hk
  have hr : Module.finrank K (LinearMap.range g) ≤ 1 := by
    simpa using (LinearMap.range g).finrank_le
  have ht := g.finrank_range_add_finrank_ker
  omega

 theorem missingCount_swap_le (π : Perm V) (P : Set V) (a b : V) :
    missingCount (π * swap a b) P ≤ missingCount π P + 1 := by
  let f : (V → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun c => c a - c b
      map_add' := by intro x y; simp only [Pi.add_apply]; ring
      map_smul' := by intro r x; simp only [Pi.smul_apply, smul_sub, RingHom.id_apply] }
  have hr : Module.finrank (ZMod 2) (colorSpace (π * swap a b) P) ≤
      Module.finrank (ZMod 2) (colorSpace π P) + 1 := by
    apply finrank_comparison _ _ f
    intro c hc he
    have hab : c a = c b := sub_eq_zero.mp he
    refine ⟨?_,hc.2⟩
    intro i
    have ht := hc.1 (swap a b i)
    simpa only [Perm.mul_apply,swap_apply_self] using ht.trans (by
      by_cases hi : i = a
      · subst i; simpa using hab.symm
      by_cases hi' : i = b
      · subst i; simpa using hab
      rw [swap_apply_of_ne_of_ne hi hi'])
  have hc (σ : Perm V) : missingCount σ P = Module.finrank (ZMod 2) (colorSpace σ P) := by
    have h1 := card_colorSpace σ P
    have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := colorSpace σ P)
    have he : (2:ℕ) ^ missingCount σ P = 2 ^ Module.finrank (ZMod 2) (colorSpace σ P) := by
      rw [← h1]
      simpa using h2
    exact Nat.pow_right_injective (by decide : 1 < (2:ℕ)) he
  simpa only [hc] using hr

 theorem weight_swap_le (π : Perm V) (P : Set V) (a b : V) :
    (2:ℝ) ^ missingCount (π * swap a b) P ≤ 2 * (2:ℝ) ^ missingCount π P := by
  calc
    _ ≤ (2:ℝ) ^ (missingCount π P + 1) :=
      pow_le_pow_right₀ (by norm_num) (missingCount_swap_le π P a b)
    _ = _ := by rw [pow_succ]; ring

end

open Equiv
variable {V : Type*} [Fintype V]

omit [Fintype V] in
lemma missing_apply (π : Perm V) (P : Set V) (i : V) :
    π i ∈ MissingSet π P ↔ i ∈ MissingSet π P := by
  simp only [MissingSet,Set.mem_ofPred_eq,classOf_apply]

end Heisenberg.Cycle
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FiniteHistories
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical

open scoped BigOperators Classical
namespace Heisenberg.Exposure

variable {I B : Type*} [Fintype I] [Fintype B]

omit [Fintype B] in
lemma productWeight_nonneg (w : I → B → ℝ) (hw : ∀ i b, 0 ≤ w i b) (c : I → B) :
    0 ≤ productWeight w c := Finset.prod_nonneg fun i _ => hw i (c i)

omit [Fintype I] [Fintype B] in
lemma merge_left (M : I → Prop) [DecidablePred M] (a : {i // M i} → B)
    (b : {i // ¬M i} → B) (i : {i // M i}) : merge M a b i = a i := by
  simp [merge,Equiv.piEquivPiSubtypeProd,i.property]

omit [Fintype I] [Fintype B] in
lemma merge_right (M : I → Prop) [DecidablePred M] (a : {i // M i} → B)
    (b : {i // ¬M i} → B) (i : {i // ¬M i}) : merge M a b i = b i := by
  simp [merge,Equiv.piEquivPiSubtypeProd,i.property]

omit [Fintype B] in
lemma productWeight_merge (w : I → B → ℝ) (M : I → Prop) [DecidablePred M]
    (a : {i // M i} → B) (b : {i // ¬M i} → B) :
    productWeight w (merge M a b) =
      productWeight (fun i : {i // M i} => w i) a *
        productWeight (fun i : {i // ¬M i} => w i) b := by
  rw [productWeight, ← Fintype.prod_subtype_mul_prod_subtype M]
  simp only [merge_left,merge_right,productWeight]


end Heisenberg.Exposure

open scoped Classical

namespace Heisenberg.LayeredExchange
variable {T V : Type*}
lemma wiring_update_swap [DecidableEq T] [DecidableEq V]
    (s : Equiv.Perm T) (σ : T → Equiv.Perm V) (t : T) (u v : V) :
    wiring s (Function.update σ t (Equiv.swap u v * σ t)) =
      Equiv.swap (s t,u) (s t,v) * wiring s σ := by
  have hc : Equiv.prodCongr s (Equiv.refl V) * Equiv.swap (t,u) (t,v) =
      Equiv.swap (s t,u) (s t,v) * Equiv.prodCongr s (Equiv.refl V) := by
    apply Equiv.ext
    intro z
    change (s (Equiv.swap (t,u) (t,v) z).1, (Equiv.swap (t,u) (t,v) z).2) =
      Equiv.swap (s t,u) (s t,v) (s z.1,z.2)
    by_cases hu : z = (t,u)
    · subst z; simp
    by_cases hv : z = (t,v)
    · subst z; simp
    have hu' : (s z.1,z.2) ≠ (s t,u) := by
      intro he; apply hu; exact Prod.ext (s.injective (congrArg Prod.fst he)) (by simpa using congrArg (fun w : T × V => w.2) he)
    have hv' : (s z.1,z.2) ≠ (s t,v) := by
      intro he; apply hv; exact Prod.ext (s.injective (congrArg Prod.fst he)) (by simpa using congrArg (fun w : T × V => w.2) he)
    rw [Equiv.swap_apply_of_ne_of_ne hu hv,Equiv.swap_apply_of_ne_of_ne hu' hv']
  unfold wiring
  rw [fibers_update,fibers_swap,← mul_assoc,hc,mul_assoc]

end Heisenberg.LayeredExchange

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LayerEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical

open Filter Topology
open scoped RealInnerProductSpace Classical
namespace Heisenberg.MeshEnergy
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable [CompleteSpace E]

lemma square_derivative {F : ℝ → Op (E:=E)} {D : Op (E:=E)}
    (h0 : F 0 = 1) (hD : HasDerivAt F D 0) :
    HasDerivAt (fun t => (ContinuousLinearMap.adjoint (F t)) * F t)
      (ContinuousLinearMap.adjoint D + D) 0 := by
  have ha := (ContinuousLinearMap.adjoint (𝕜:=ℝ) (E:=E) (F:=E)).toContinuousLinearEquiv.hasFDerivAt.comp_hasDerivAt 0 hD
  change HasDerivAt (fun t => ContinuousLinearMap.adjoint (F t)) (ContinuousLinearMap.adjoint D) 0 at ha
  have hh := ha.clm_comp hD
  change HasDerivAt (fun t => (ContinuousLinearMap.adjoint (F t))*F t)
    ((ContinuousLinearMap.adjoint D)*F 0 + (ContinuousLinearMap.adjoint (F 0))*D) 0 at hh
  simpa only [h0,ContinuousLinearMap.adjoint_one,one_mul,mul_one] using hh

theorem uniform_energy_error {F : ℝ → Op (E:=E)} {D : Op (E:=E)}
    (h0 : F 0 = 1) (hD : HasDerivAt F D 0) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ t in 𝓝 (0:ℝ), ∀ v : E,
      |‖F t v‖^2 - ‖v‖^2 - 2*t*⟪v,D v⟫| ≤ ε*|t| *‖v‖^2 := by
  have hh := (square_derivative h0 hD).isLittleO.def hε
  filter_upwards [hh] with t ht
  intro v
  let R : Op (E:=E) := (ContinuousLinearMap.adjoint (F t))*F t - 1 -
    t • (ContinuousLinearMap.adjoint D + D)
  have hR : ‖R‖ ≤ ε*|t| := by
    simpa only [h0,sub_zero,ContinuousLinearMap.adjoint_one,mul_one,
      Real.norm_eq_abs] using ht
  have he : ⟪v,R v⟫ = ‖F t v‖^2 - ‖v‖^2 - 2*t*⟪v,D v⟫ := by
    simp only [R,_root_.sub_apply,mul_apply_eq_comp,
      one_apply_eq_self,_root_.smul_apply,
      _root_.add_apply,inner_sub_right,inner_smul_right,
      inner_add_right,ContinuousLinearMap.adjoint_inner_right,real_inner_self_eq_norm_sq,
      real_inner_comm (D v) v]
    ring
  rw [← he]
  calc
    _ ≤ ‖v‖ * ‖R v‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖v‖ * (‖R‖*‖v‖) := mul_le_mul_of_nonneg_left (R.le_opNorm v) (norm_nonneg _)
    _ ≤ ‖v‖ * ((ε*|t|)*‖v‖) := by gcongr
    _ = _ := by ring

omit [CompleteSpace E] in
lemma sweep_derivative (D : ℕ → Op (E:=E)) (n : ℕ) :
    HasDerivAt (sweep D n) (∑ i ∈ Finset.range n, D i) 0 := by
  induction n with
  | zero => simpa [sweep] using hasDerivAt_const (0:ℝ) (1 : Op (E:=E))
  | succ n ih =>
    have hd : HasDerivAt (fun t : ℝ => (1:Op (E:=E))+t • D n) (D n) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).smul_const (D n) |>.const_add 1
    have hh := hd.clm_comp ih
    change HasDerivAt (sweep D (n+1)) (D n * sweep D n 0 +
      (1+(0:ℝ) • D n) * (∑ i ∈ Finset.range n, D i)) 0 at hh
    simpa only [sweep_zero,zero_smul,add_zero,zero_add,mul_one,one_mul,Finset.sum_range_succ,add_comm] using hh

end Heisenberg.MeshEnergy
namespace Heisenberg.MeshPair
open MeshEnergy
open scoped RealInnerProductSpace Classical
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma generator_apply (w v : E) : generator w v = (-⟪w,v⟫/2) • w := by
  simp only [generator,_root_.smul_apply,ContinuousLinearMap.smulRight_apply,innerSL_apply_apply,smul_smul]
  congr 1
  ring

lemma generator_energy (w v : E) : -⟪v,generator w v⟫ = (1/2:ℝ)*⟪w,v⟫^2 := by
  rw [generator_apply,inner_smul_right,real_inner_comm v w]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma edge_inner (I : Set V) (a b : V) (v : EuclideanSpace ℝ V) :
    ⟪edgeVector I a b,v⟫ = (if a ∈ I then v.ofLp a else 0) -
      (if b ∈ I then v.ofLp b else 0) := by
  simp only [edgeVector,inner_sub_left,EuclideanSpace.inner_single_left]
  split_ifs <;> simp

end Heisenberg.MeshPair
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_KilledContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair
open scoped RealInnerProductSpace Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma killedCoin_generator (I : Set V) {a b : V} (hab : a ≠ b) (t : ℝ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ I, v.ofLp i = 0) :
    killedCoin I a b t v = (1+t • generator (edgeVector I a b)) v := by
  ext i
  simp only [killedCoin,killedPermutation,PiLp.add_apply,PiLp.smul_apply,
    smul_eq_mul,_root_.add_apply,one_apply_eq_self,
    _root_.smul_apply,generator_apply]
  simp only [edge_inner]
  simp only [edgeVector,PiLp.sub_apply,PiLp.single_apply,Equiv.symm_swap]
  by_cases hi : i = a
  · subst i
    rw [Equiv.swap_apply_left]
    by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [ha,hb,hab,hv] <;> ring
  · by_cases hi' : i = b
    · subst i
      rw [Equiv.swap_apply_right]
      by_cases ha : a ∈ I <;> by_cases hb : b ∈ I <;> simp [ha,hb,Ne.symm hab,hv] <;> ring
    · rw [Equiv.swap_apply_of_ne_of_ne hi hi']
      by_cases hI : i ∈ I <;> simp [hi,hi',hI,hv]
      ring

end Heisenberg.MeshPair

namespace Heisenberg.MatrixContraction

variable {V : Type*} [Fintype V]

lemma DoublySubstochastic.mul {U W : Matrix V V ℝ}
    (hU : DoublySubstochastic U) (hW : DoublySubstochastic W) :
    DoublySubstochastic (U * W) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hU.nonneg i k) (hW.nonneg k j))
  · intro i
    change (∑ j, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_right (hU.nonneg i k) (hW.row k))).trans (hU.row i)
  · intro j
    change (∑ i, ∑ k, U i k * W k j) ≤ 1
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul]
    exact (Finset.sum_le_sum (fun k _ =>
      mul_le_of_le_one_left (hW.nonneg k j) (hU.col k))).trans (hW.col j)

lemma weighted_square (w f : V → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i, w i * f i) ^ 2 ≤ (∑ i, w i) * ∑ i, w i * f i ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i)) (fun i => Real.sqrt (w i) * f i)
  simpa only [← mul_assoc, Real.mul_self_sqrt (hw _), mul_pow,
    Real.sq_sqrt (hw _)] using h

theorem contraction {U : Matrix V V ℝ} (hU : DoublySubstochastic U) (f : V → ℝ) :
    ∑ i, ((U.mulVec f) i) ^ 2 ≤ ∑ i, (f i) ^ 2 := by
  calc
    _ ≤ ∑ i, (∑ j, U i j) * (∑ j, U i j * f j ^ 2) := by
      exact Finset.sum_le_sum (fun i _ => weighted_square (U i) f (hU.nonneg i))
    _ ≤ ∑ i, ∑ j, U i j * f j ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_of_le_one_left
        (Finset.sum_nonneg (fun j _ => mul_nonneg (hU.nonneg i j) (sq_nonneg _))) (hU.row i)
    _ = ∑ j, (∑ i, U i j) * f j ^ 2 := by
      rw [Finset.sum_comm]
      simp_rw [Finset.sum_mul]
    _ ≤ _ := Finset.sum_le_sum (fun j _ => mul_le_of_le_one_left (sq_nonneg _) (hU.col j))

theorem of_partial_permutation (p : V → Option V)
    (hp : ∀ i j a, p i = some a → p j = some a → i = j) :
    DoublySubstochastic (fun i j => if p j = some i then 1 else 0) := by
  constructor
  · intro i j; split_ifs <;> norm_num
  · intro i
    have hc : (Finset.univ.filter fun j => p j = some i).card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro j hj k hk
      exact hp j k i (Finset.mem_filter.mp hj).2 (Finset.mem_filter.mp hk).2
    simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      Nat.cast_le_one] using (show ((Finset.univ.filter fun j => p j = some i).card : ℝ) ≤ 1 by
        exact_mod_cast hc)
  · intro j
    cases hj : p j with
    | none => simp
    | some i => simp

theorem weighted_average {I : Type*} [Fintype I] (w : I → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hs : ∑ a, w a = 1) (U : I → Matrix V V ℝ)
    (hU : ∀ a, DoublySubstochastic (U a)) :
    DoublySubstochastic (fun i j => ∑ a, w a * U a i j) := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun a _ => mul_nonneg (hw a) ((hU a).nonneg i j))
  · intro i
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).row i))
      _ = 1 := hs
  · intro j
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    calc
      _ ≤ ∑ a, w a := Finset.sum_le_sum (fun a _ =>
        mul_le_of_le_one_right (hw a) ((hU a).col j))
      _ = 1 := hs

end Heisenberg.MatrixContraction

namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction Matrix
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma euclideanMap_contraction (K : Matrix V V ℝ) (hK : DoublySubstochastic K)
    (v : EuclideanSpace ℝ V) : ‖euclideanMap K v‖ ≤ ‖v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  exact contraction hK v.ofLp

lemma killedMatrix_apply (D : Set V) (σ : Equiv.Perm V) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ D,v.ofLp i=0) :
    euclideanMap (killedMatrix D σ) v = killedPermutation D σ v := by
  ext i
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct,killedMatrix,killedPermutation]
  rw [Finset.sum_eq_single (σ.symm i)]
  · by_cases hi : i ∈ D <;> by_cases hj : σ.symm i ∈ D <;> simp [hi,hj,hv]
  · intro j _ hj
    have hh : i ≠ σ j := by intro he; apply hj; exact (σ.symm_apply_eq.mpr he).symm
    simp [hh]
  · simp

lemma killedMatrix_identity (D : Set V) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ D,v.ofLp i=0) : euclideanMap (killedMatrix D 1) v=v := by
  rw [killedMatrix_apply D 1 v hv]
  ext i
  by_cases hi : i ∈ D
  · simp only [killedPermutation,hi,ite_true]
    rfl
  · simp [killedPermutation,hi,hv]

lemma residual_quiet (H D : Set V) (a b : V) (p : ℝ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ D,v.ofLp i=0) :
    euclideanMap (residualMatrix D (a ∉ H ∨ b ∉ H) false a b p) v =
      if a ∈ H ∧ b ∈ H then killedCoin D a b (2*p) v else v := by
  by_cases hh : a ∈ H ∧ b ∈ H
  · simp only [residualMatrix,show ¬(a ∉ H ∨ b ∉ H) by tauto,ite_false,ite_eq_left hh]
    have he : euclideanMap ((1-p) • killedMatrix D 1 + p • killedMatrix D (Equiv.swap a b)) v =
        (1-p) • euclideanMap (killedMatrix D 1) v + p • euclideanMap (killedMatrix D (Equiv.swap a b)) v := by
      ext i
      simp only [euclideanMap_apply,Matrix.add_mulVec,Matrix.smul_mulVec,PiLp.add_apply,
        PiLp.smul_apply,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    rw [he,killedMatrix_identity D v hv,killedMatrix_apply D _ v hv]
    simp [killedCoin]
  · simp only [residualMatrix,show a ∉ H ∨ b ∉ H by tauto,ite_true,Bool.false_eq_true,
      ite_false,ite_eq_right hh]
    exact killedMatrix_identity D v hv

end Heisenberg.MeshPair
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_QuietSweeps
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.MeshPair

section
open Heisenberg.MeshEnergy Heisenberg.MatrixContraction Matrix Filter Topology
open scoped RealInnerProductSpace
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma residual_supported (D : Set V) (R : Prop) (c : Bool) (a b : V) (p : ℝ)
    (v : EuclideanSpace ℝ V) (i : V) (hi : i ∉ D) :
    (euclideanMap (residualMatrix D R c a b p) v).ofLp i=0 := by
  have hh (σ : Equiv.Perm V) : ∀ j,killedMatrix D σ i j=0 := by
    intro j
    by_cases he : i=σ j
    · have hn : σ j ∉ D := he ▸ hi
      simp [killedMatrix,hn]
    · simp [killedMatrix,he]
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct,residualMatrix]
  split_ifs <;> simp [hh,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]

lemma quietSweep_supported (H D : Set V) (a b : ℕ → V) (t : ℝ) (n : ℕ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ D,v.ofLp i=0) :
    ∀ i ∉ D,(quietSweep H D a b t n v).ofLp i=0 := by
  cases n with
  | zero => exact hv
  | succ n => exact residual_supported D _ _ _ _ _ _

lemma quietSweep_eq (H D : Set V) (a b : ℕ → V) (n : ℕ)
    (hab : ∀ i,i<n → a i ≠ b i) (t : ℝ) (v : EuclideanSpace ℝ V)
    (hv : ∀ i ∉ D,v.ofLp i=0) :
    quietSweep H D a b t n v=sweep (maskedGenerator H D a b) n t v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [quietSweep,residual_quiet H D (a n) (b n) (t/2) _
      (quietSweep_supported H D a b t n v hv)]
    have he : 2*(t/2)=t := by ring
    rw [he]
    by_cases hh : a n ∈ H ∧ b n ∈ H
    · rw [ite_eq_left hh,killedCoin_generator D (hab n (by omega)) t _
        (quietSweep_supported H D a b t n v hv),ih (fun i hi => hab i (by omega))]
      simp only [sweep,maskedGenerator,ite_eq_left hh,mul_apply_eq_comp]
    · rw [ite_eq_right hh,ih (fun i hi => hab i (by omega))]
      simp only [sweep,maskedGenerator,ite_eq_right hh,smul_zero,add_zero,one_mul]

lemma masked_dirichlet (H D : Set V) (a b : ℕ → V) (n : ℕ)
    (v : EuclideanSpace ℝ V) (hv : ∀ i ∉ D,v.ofLp i=0) :
    -⟪v,(∑ i ∈ Finset.range n,maskedGenerator H D a b i) v⟫ =
      (1/2:ℝ)*quietEnergy H a b n v := by
  simp only [_root_.sum_apply,inner_sum,←Finset.sum_neg_distrib,quietEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  unfold maskedGenerator
  split_ifs
  · rw [generator_energy,edge_inner]
    have he (j : V) : (if j ∈ D then v.ofLp j else 0)=v.ofLp j := by
      split_ifs with h
      · rfl
      · exact (hv j h).symm
    simp only [he]
  · simp

theorem quietSweep_energy (a b : ℕ → V) (n : ℕ) (hab : ∀ i,i<n → a i ≠ b i)
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),∀ (H D : Set V) (v : EuclideanSpace ℝ V),
      (∀ i ∉ D,v.ofLp i=0) →
      |‖quietSweep H D a b t n v‖^2-‖v‖^2+t*quietEnergy H a b n v| ≤ ε * |t| * ‖v‖^2 := by
  have hh : ∀ H D : Set V,∀ᶠ t in 𝓝 (0:ℝ),∀ (v : EuclideanSpace ℝ V),
      (∀ i ∉ D,v.ofLp i=0) →
      |‖quietSweep H D a b t n v‖^2-‖v‖^2+t*quietEnergy H a b n v| ≤ ε * |t| * ‖v‖^2 := by
    intro H D
    have h := uniform_energy_error (sweep_zero (maskedGenerator H D a b) n)
      (sweep_derivative (maskedGenerator H D a b) n) hε
    filter_upwards [h] with t ht
    intro v hv
    rw [quietSweep_eq H D a b n hab t v hv]
    have he := masked_dirichlet H D a b n v hv
    convert ht v using 1
    congr 1
    nlinarith [congrArg (fun z : ℝ => t*z) he]
  exact Filter.eventually_all.mpr fun H => Filter.eventually_all.mpr (hh H)

end

open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma killedBetween_substochastic (D E : Set V) (σ : Equiv.Perm V) :
    DoublySubstochastic (killedBetween D E σ) := by
  let p : V → Option V := fun j => if j∈D ∧ σ j∈E then some (σ j) else none
  have hp : ∀ i j a,p i=some a → p j=some a → i=j := by
    intro i j a hi hj
    dsimp [p] at hi hj
    split_ifs at hi hj
    exact σ.injective ((Option.some.inj hi).trans (Option.some.inj hj).symm)
  have hh := of_partial_permutation p hp
  have he : killedBetween D E σ = fun i j => if p j=some i then 1 else 0 := by
    funext i j
    dsimp [killedBetween,p]
    by_cases hj : j∈D
    · by_cases he : σ j∈E
      · simp only [hj,he,and_self,ite_true,true_and,Option.some.injEq]
        by_cases h : i=σ j
        · subst i; simp [he]
        · simp [h,Ne.symm h]
      · simp only [hj,he,and_false,ite_false,true_and,reduceCtorEq,ite_false]
        split_ifs with h
        · exact False.elim (he (h.2 ▸ h.1))
        · rfl
    · simp [hj]
  rw [he]
  convert hh using 1
  apply Iff.of_eq
  apply congrArg DoublySubstochastic
  funext i j
  split_ifs <;> rfl

omit [Fintype V] in
lemma killedBetween_same (D : Set V) (σ : Equiv.Perm V) :
    killedBetween D D σ=killedMatrix D σ := by
  ext i j
  simp only [killedBetween,killedMatrix]
  by_cases h : i=σ j
  · subst i; simp
  · simp [h]

lemma residualBetween_substochastic (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) (hp : 0≤p) (hp1 : p≤1) :
    DoublySubstochastic (residualBetween D E revealed c a b p) := by
  by_cases hr : revealed
  · simp only [residualBetween,ite_eq_left hr]
    exact killedBetween_substochastic _ _ _
  · simp only [residualBetween,ite_eq_right hr]
    have h := weighted_average (fun z : Bool => if z then p else 1-p)
      (by intro z; cases z <;> simp <;> linarith)
      (by simp) (fun z => killedBetween D E (if z then Equiv.swap a b else 1))
      (fun _ => killedBetween_substochastic _ _ _)
    have he : (1-p) • killedBetween D E 1 + p • killedBetween D E (Equiv.swap a b) =
        (fun i j => ∑ z : Bool,(if z then p else 1-p)*killedBetween D E (if z then Equiv.swap a b else 1) i j) := by
      ext i j
      simp [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,add_comm]
    rw [he]
    exact h

omit [Fintype V] in
lemma residualBetween_same (D : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) :
    residualBetween D D revealed c a b p=residualMatrix D revealed c a b p := by
  unfold residualBetween residualMatrix
  simp only [killedBetween_same]

lemma residualBetween_supported (D E : Set V) (revealed : Prop)
    (c : Bool) (a b : V) (p : ℝ) (v : EuclideanSpace ℝ V) :
    ∀ i∉E,(euclideanMap (residualBetween D E revealed c a b p) v).ofLp i=0 := by
  intro i hi
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  have hz : ∀ σ : Equiv.Perm V,killedBetween D E σ i j=0 := by
    intro σ
    simp [killedBetween,hi]
  by_cases hr : revealed <;> simp [residualBetween,hr,Matrix.add_apply,Matrix.smul_apply,hz]

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma holeCut_transport (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (base : T → Bool)
    (P : Set (T×V)) (t : T) (v : V) :
    (if base t then τ t else 1) v∈holeCut s τ base P (s t) ↔
      v∈holeCut s τ base P t := by
  exact not_congr (missing_apply (layerHistory s τ base) P (t,v))

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma holeCut_quiet (s : Equiv.Perm T) (τ : T → Equiv.Perm V) (base : T → Bool)
    (P : Set (T×V)) (t : T) (ht : base t=false) :
    holeCut s τ base P (s t)=holeCut s τ base P t := by
  ext v
  simpa only [ht,Bool.false_eq_true,↓reduceIte,Equiv.Perm.one_apply] using
    holeCut_transport s τ base P t v

omit [Fintype T] [Fintype V] in
lemma layerRevealed_swap (a b : T → V) (A : Set (T×V)) (t : T) (hab : a t≠b t) :
    layerRevealed (fun i => Equiv.swap (a i) (b i)) A t ↔ (t,a t)∈A ∨ (t,b t)∈A := by
  constructor
  · rintro ⟨v,hv,hn⟩
    by_cases ha : v=a t
    · exact Or.inl (ha ▸ hv)
    · have hb : v=b t := by
        by_contra hb
        exact hn (Equiv.swap_apply_of_ne_of_ne ha hb)
      exact Or.inr (hb ▸ hv)
  · rintro (ha|hb)
    · exact ⟨a t,ha,by simpa using hab.symm⟩
    · exact ⟨b t,hb,by simpa using hab⟩

omit [Fintype T] [Fintype V] in
lemma exposedStep_quiet (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (t : T)
    (ht : base t=false) (hab : a t≠b t) :
    exposedStep s a b base P I p t =
      residualMatrix (holeCut s (fun i => Equiv.swap (a i) (b i)) base P t∩I)
        (a t∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P t ∨
          b t∉holeCut s (fun i => Equiv.swap (a i) (b i)) base P t)
        false (a t) (b t) (p t) := by
  unfold exposedStep
  dsimp only
  rw [holeCut_quiet s _ base P t ht,ht,residualBetween_same]
  congr 1
  rw [layerRevealed_swap a b _ t hab]
  simp only [holeCut,Set.mem_ofPred_eq,not_not]

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma holeCut_quiet_segment (s : Equiv.Perm T) (τ : T → Equiv.Perm V)
    (base : T → Bool) (P : Set (T×V)) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hb : ∀ i,i<n → base (r i)=false) :
    holeCut s τ base P (r n)=holeCut s τ base P (r 0) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [hr n (by omega),holeCut_quiet s τ base P (r n) (hb n (by omega))]
    exact ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))

omit [Fintype T] in

theorem exposedSweep_quiet (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (r : ℕ → T) (n : ℕ) (t : ℝ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (hb : ∀ i,i<n → base (r i)=false)
    (hab : ∀ i,i<n → a (r i)≠b (r i)) (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I (fun _ => t/2) r n v =
      quietSweep (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0))
        (holeCut s (fun i => Equiv.swap (a i) (b i)) base P (r 0)∩I)
        (a ∘ r) (b ∘ r) t n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exposedSweep,exposedStep_quiet s a b base P I _ (r n) (hb n (by omega))
      (hab n (by omega)),holeCut_quiet_segment s _ base P r n
      (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega)),
      ih (fun i hi => hr i (by omega)) (fun i hi => hb i (by omega))
        (fun i hi => hab i (by omega))]
    rfl

end Heisenberg.Exposure
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ExposedEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open Matrix
open scoped Classical
open scoped BigOperators Classical
open scoped Classical
open scoped Classical
open Filter
open scoped Classical
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical

namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedStep_substochastic (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1) (t : T) :
    Heisenberg.MatrixContraction.DoublySubstochastic (exposedStep s a b base P I p t) :=
  residualBetween_substochastic _ _ _ _ _ _ _ (hp t).1 (hp t).2

omit [Fintype T] in
lemma exposedSweep_contraction (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    (r : ℕ → T) (n : ℕ) (v : EuclideanSpace ℝ V) :
    ‖exposedSweep s a b base P I p r n v‖≤‖v‖ := by
  induction n with
  | zero => rfl
  | succ n ih => exact (euclideanMap_contraction _ (exposedStep_substochastic s a b base P I p hp _) _).trans ih

omit [Fintype T] [Fintype V] [DecidableEq V] in
lemma quietEnergy_le_card (H : Set V) (a b : ℕ → V) (n : ℕ) (v : EuclideanSpace ℝ V)
    (hv : ∀ j,0≤v.ofLp j ∧ v.ofLp j≤1) : _root_.OAI.Heisenberg.MeshPair.quietEnergy H a b n v≤n := by
  apply le_trans (Finset.sum_le_sum (fun i _ => ?_)) (by simp : (∑ _i∈Finset.range n,(1:ℝ))=n).le
  split_ifs
  · nlinarith [(hv (a i)).1,(hv (a i)).2,(hv (b i)).1,(hv (b i)).2,
      mul_nonneg (hv (a i)).1 (hv (b i)).1]
  · norm_num

end Heisenberg.Exposure

open scoped BigOperators Classical
namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

omit [Fintype I] in
lemma join_update (i : I) (b b' : Bool) (d : {j // j ≠ i} → Bool) :
    Function.update (join i b d) i b' = join i b' d := by
  funext j
  by_cases h : j = i
  · subst j; simp
  · simpa only [Function.update_of_ne h] using (join_ne i b d ⟨j,h⟩).trans (join_ne i b' d ⟨j,h⟩).symm

lemma weight_join (p : I → ℝ) (i : I) (b : Bool) (d : {j // j ≠ i} → Bool) :
    weight p (join i b d) = (if b then p i else 1-p i) * weight (fun j : {j // j ≠ i} => p j) d := by
  unfold weight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ i]
  simp only [join_at,join_ne]

lemma sum_split (p : I → ℝ) (F : (I → Bool) → ℝ) (i : I) :
    (∑ c, weight p c * F c) =
      ∑ d : {j // j ≠ i} → Bool, weight (fun j : {j // j ≠ i} => p j) d *
        ((1-p i)*F (join i false d) + p i*F (join i true d)) := by
  rw [← (Equiv.funSplitAt i Bool).symm.sum_comp]
  change (∑ q : Bool × ({j // j ≠ i} → Bool), weight p (join i q.1 q.2) * F (join i q.1 q.2)) = _
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, weight_join, Bool.false_eq_true, ↓reduceIte]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring

lemma scalar_bound {κ p W₀ W₁ : ℝ} (hκ : 1 ≤ κ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hW₁ : 0 ≤ W₁) (hW : W₁ ≤ κ*W₀) :
    W₁ ≤ κ*((1-p)*W₀+p*W₁) := by
  have h1 := mul_le_mul_of_nonneg_left hW (sub_nonneg.mpr hp1)
  have h2 := mul_le_mul_of_nonneg_left (show W₁ ≤ κ*W₁ by nlinarith) hp
  nlinarith

lemma weight_nonneg (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (c : I → Bool) :
    0 ≤ weight p c := by
  apply Finset.prod_nonneg
  intro i _
  split_ifs <;> linarith [(hp i).1,(hp i).2]

lemma one_coin (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {κ : ℝ} (hκ : 1 ≤ κ)
    (W G : (I → Bool) → ℝ) (i : I)
    (hW : ∀ c, 0 ≤ W c) (hG : ∀ c, 0 ≤ G c)
    (hins : ∀ c, W (Function.update c i true) ≤ κ*W (Function.update c i false))
    (hGi : ∀ c, G (Function.update c i true) = G (Function.update c i false)) :
    (∑ c, weight p c * ((if c i then W c else 0)*G c)) ≤
      κ*p i * ∑ c, weight p c*(W c*G c) := by
  rw [sum_split, sum_split, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have hi := hins (join i false d)
  have hg := hGi (join i false d)
  simp only [join_update] at hi hg
  simp only [join_at,Bool.false_eq_true,↓reduceIte,zero_mul,mul_zero,zero_add]
  rw [hg]
  have hb := scalar_bound hκ (hp i).1 (hp i).2 (hW _) hi
  have hn := mul_le_mul_of_nonneg_left hb (mul_nonneg (hp i).1 (hG (join i false d)))
  have hf := mul_le_mul_of_nonneg_left hn
    (weight_nonneg (fun j : {j // j ≠ i} => p j) (fun j => hp j) d)
  nlinarith

lemma test_nonneg (s : Finset I) (c : I → Bool) : 0 ≤ test s c := by
  unfold test; split_ifs <;> norm_num

lemma test_update {s : Finset I} {i : I} (hi : i ∉ s) (c : I → Bool) (b : Bool) :
    test s (Function.update c i b) = test s c := by
  unfold test
  congr 1
  apply propext
  constructor <;> intro h j hj
  · have hjn : j ≠ i := by intro he; subst j; exact hi hj
    simpa only [Function.update_of_ne hjn] using h j hj
  · rw [Function.update_of_ne (show j ≠ i by intro he; subst j; exact hi hj)]
    exact h j hj

lemma test_insert (s : Finset I) (i : I) (c : I → Bool) :
    test (insert i s) c = (if c i then 1 else 0)*test s c := by
  simp only [test,Finset.forall_mem_insert]
  split_ifs <;> simp_all

theorem factorial_bound (p : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) {κ : ℝ} (hκ : 1 ≤ κ)
    (W : (I → Bool) → ℝ) (hW : ∀ c, 0 ≤ W c)
    (hins : ∀ c i, W (Function.update c i true) ≤ κ*W (Function.update c i false))
    (s : Finset I) :
    (∑ c, weight p c*(W c*test s c)) ≤ (∏ i ∈ s, κ*p i) * ∑ c, weight p c*W c := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hc := one_coin p hp hκ W (test s) i hW (test_nonneg s)
      (fun c => hins c i) (fun c => by rw [test_update hi,test_update hi])
    have he : (∑ c, weight p c*(W c*test (insert i s) c)) =
        ∑ c, weight p c*((if c i then W c else 0)*test s c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [test_insert]
      cases c i <;> simp
    rw [he]
    exact hc.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih (mul_nonneg (by linarith) (hp i).1))

theorem factorial_bound_rates (p κ : I → ℝ) (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1)
    (hκ : ∀ i,1 ≤ κ i) (W : (I → Bool) → ℝ) (hW : ∀ c, 0 ≤ W c)
    (hins : ∀ c i, W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (s : Finset I) :
    (∑ c, weight p c*(W c*test s c)) ≤ (∏ i ∈ s, κ i*p i) * ∑ c, weight p c*W c := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    have hc := one_coin p hp (hκ i) W (test s) i hW (test_nonneg s)
      (fun c => hins c i) (fun c => by rw [test_update hi,test_update hi])
    have he : (∑ c, weight p c*(W c*test (insert i s) c)) =
        ∑ c, weight p c*((if c i then W c else 0)*test s c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [test_insert]
      cases c i <;> simp
    rw [he]
    exact hc.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left ih
        (mul_nonneg (by linarith [hκ i]) (hp i).1))

lemma test_eq_prod (s : Finset I) (c : I → Bool) :
    test s c = ∏ i ∈ s, if c i then (1:ℝ) else 0 := by
  induction s using Finset.induction_on with
  | empty => simp [test]
  | @insert i s hi ih => rw [test_insert,Finset.prod_insert hi,ih]

lemma weight_test_sum (p : I → ℝ) (s : Finset I) :
    (∑ c,weight p c*test s c) = ∏ i ∈ s,p i := by
  have he (c : I → Bool) : weight p c*test s c =
      ∏ i, if c i then p i else if i ∈ s then 0 else 1-p i := by
    rw [test_eq_prod]
    have ht : (∏ i ∈ s, if c i then (1:ℝ) else 0) = ∏ i,if i ∈ s then (if c i then (1:ℝ) else 0) else 1 := by
      simp only [Finset.prod_ite_mem,Finset.univ_inter]
    rw [ht,weight,←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hi : i ∈ s <;> cases c i <;> simp [hi]
  simp_rw [he]
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p i else if i ∈ s then 0 else 1-p i)]
  simp only [Fintype.sum_bool,Bool.false_eq_true,↓reduceIte]
  have he : (fun i => p i + if i ∈ s then (0:ℝ) else 1-p i) = fun i => if i ∈ s then p i else 1 := by
    funext i
    split_ifs <;> ring
  rw [he]
  simp only [Finset.prod_ite_mem,Finset.univ_inter]

end Heisenberg.Bernoulli
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CycleWeights
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Matrix
open Filter
open scoped Classical
open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped BigOperators Classical

namespace Heisenberg.Cycle
open Equiv
variable {V : Type*} [Fintype V]

lemma weight_left_swap_le (π : Perm V) (P : Set V) (a b : V) :
    (2:ℝ)^missingCount (swap a b * π) P ≤ 2*(2:ℝ)^missingCount π P := by
  have he : swap a b * π = π * swap (π.symm a) (π.symm b) := by
    apply Equiv.ext
    intro x
    by_cases ha : x = π.symm a
    · subst x; simp
    by_cases hb : x = π.symm b
    · subst x; simp
    have ha' : π x ≠ a := fun h => ha (π.injective (h.trans (π.apply_symm_apply a).symm))
    have hb' : π x ≠ b := fun h => hb (π.injective (h.trans (π.apply_symm_apply b).symm))
    simp [Perm.mul_apply,swap_apply_of_ne_of_ne ha hb,swap_apply_of_ne_of_ne ha' hb']
  rw [he]
  exact weight_swap_le π P _ _
end Heisenberg.Cycle

namespace Heisenberg.Exposure

section
open Heisenberg.Cycle Heisenberg.LayeredExchange Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] [Fintype V] in
lemma layerHistory_insert (s : Equiv.Perm T) (a b : T → V) (c : T → Bool) (t : T) :
    layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t true) =
      Equiv.swap (s t,a t) (s t,b t) *
        layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t false) := by
  let σ := fun j => if Function.update c t false j then Equiv.swap (a j) (b j) else 1
  have he : (fun j => if Function.update c t true j then Equiv.swap (a j) (b j) else 1) =
      Function.update σ t (Equiv.swap (a t) (b t)*σ t) := by
    funext j
    by_cases h : j=t
    · subst j
      simp [σ]
    · simp [Function.update_of_ne h,σ]
  change wiring s _ = _ * wiring s σ
  rw [he,wiring_update_swap]

omit [Fintype T] [Fintype V] in
lemma layerWeight_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    0 ≤ layerWeight s a b P c := by unfold layerWeight; positivity

omit [Fintype T] [Fintype V] in
lemma layerWeight_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V)) (c : T → Bool) :
    1 ≤ layerWeight s a b P c := one_le_pow₀ (by norm_num)

lemma layerWeight_insertion (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (c : T → Bool) (t : T) :
    layerWeight s a b P (Function.update c t true) ≤
      2*layerWeight s a b P (Function.update c t false) := by
  unfold layerWeight
  have h := weight_left_swap_le (layerHistory s (fun j => Equiv.swap (a j) (b j)) (Function.update c t false)) P (s t,a t) (s t,b t)
  convert h using 1
  congr 2
  exact (layerHistory_insert s a b c t).trans (by
    congr 1
    apply Equiv.ext
    intro x
    simp only [Equiv.swap_apply_def]
    split_ifs <;> rfl)

lemma coin_weight_sum (p : T → ℝ) : (∑ c,weight p c)=1 := by
  simpa [Bernoulli.test] using weight_test_sum p ∅

omit [Fintype V] in
lemma layerPartition_one_le (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : 1≤layerPartition s a b P p := by
  rw [←coin_weight_sum p]
  exact Finset.sum_le_sum fun c _ => le_mul_of_one_le_right (weight_nonneg p hp c) (layerWeight_one_le s a b P c)

omit [Fintype V] in
lemma layerMass_nonneg (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (c : T → Bool) : 0≤layerMass s a b P p c := by
  exact div_nonneg (mul_nonneg (weight_nonneg p hp c) (layerWeight_nonneg s a b P c))
    (le_trans (by norm_num) (layerPartition_one_le s a b P p hp))

omit [Fintype V] in
lemma layerMass_sum (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) : (∑ c,layerMass s a b P p c)=1 := by
  simp only [layerMass,←Finset.sum_div]
  change layerPartition s a b P p / layerPartition s a b P p = 1
  exact div_self (ne_of_gt (lt_of_lt_of_le (by norm_num) (layerPartition_one_le s a b P p hp)))

theorem layer_factorial_bound (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (F : Finset T) :
    (∑ c,if ∀ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤ ∏ i ∈ F,2*p i := by
  have hz : 0<layerPartition s a b P p :=
    lt_of_lt_of_le (by norm_num) (layerPartition_one_le s a b P p hp)
  have h := factorial_bound p hp (κ:=2) (by norm_num) (layerWeight s a b P)
    (layerWeight_nonneg s a b P) (layerWeight_insertion s a b P) F
  have he : (∑ c,if ∀ i ∈ F,c i=true then layerMass s a b P p c else 0) =
      (∑ c,weight p c*(layerWeight s a b P c*Bernoulli.test F c))/layerPartition s a b P p := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro c _
    unfold Bernoulli.test layerMass
    split_ifs <;> simp
  rw [he]
  exact (div_le_iff₀ hz).mpr h

theorem layer_nonquiet_bound (s : Equiv.Perm T) (a b : T → V) (P : Set (T × V))
    (p : T → ℝ) (hp : ∀ t,0≤p t ∧ p t≤1) (F : Finset T) :
    (∑ c,if ∃ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤ ∑ i ∈ F,2*p i := by
  have h : ∀ c,(if ∃ i ∈ F,c i=true then layerMass s a b P p c else 0) ≤
      ∑ i ∈ F,if c i=true then layerMass s a b P p c else 0 := by
    intro c
    by_cases hc : ∃ i ∈ F,c i=true
    · obtain ⟨i,hi,hci⟩ := hc
      rw [ite_eq_left ⟨i,hi,hci⟩]
      calc
        _ = if c i=true then layerMass s a b P p c else 0 := by rw [ite_eq_left hci]
        _ ≤ _ := Finset.single_le_sum (f := fun j => if c j=true then layerMass s a b P p c else 0) (fun j _ => by split_ifs; exact layerMass_nonneg s a b P p hp c; exact le_rfl) hi
    · rw [ite_eq_right hc]
      exact Finset.sum_nonneg (fun j _ => by split_ifs; exact layerMass_nonneg s a b P p hp c; exact le_rfl)
  calc
    _ ≤ ∑ c,∑ i ∈ F,if c i=true then layerMass s a b P p c else 0 := Finset.sum_le_sum (fun c _ => h c)
    _ = ∑ i ∈ F,∑ c,if c i=true then layerMass s a b P p c else 0 := Finset.sum_comm
    _ ≤ _ := Finset.sum_le_sum (fun i _ => by simpa using layer_factorial_bound s a b P p hp {i})

end

open Heisenberg.MeshPair Heisenberg.Bernoulli
variable {T V : Type*} [Fintype T] [Fintype V]

omit [Fintype T] in
lemma bounded_euclidean_sq (v : EuclideanSpace ℝ V)
    (hv : ∀ j,0≤v.ofLp j ∧ v.ofLp j≤1) : ‖v‖^2≤Fintype.card V := by
  rw [EuclideanSpace.norm_sq_eq]
  apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (by simp : (∑ _j : V,(1:ℝ))=Fintype.card V).le
  rw [Real.norm_eq_abs,sq_abs]
  nlinarith [(hv j).1,(hv j).2]

theorem tilted_nonquiet_error (s : Equiv.Perm T) (a b : T → V)
    (P : Set (T×V)) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    (r : ℕ → T) (n : ℕ) {t : ℝ} (ht : 0≤t)
    (hrate : ∀ i,i<n → p (r i)=t/2) :
    (∑ base,layerMass s a b P p base *
      (if ∃ i,i<n ∧ base (r i)=true then t*n else 0)) ≤ t^2*n^2 := by
  let F := (Finset.range n).image r
  have he (base : T → Bool) : (∃ i,i<n ∧ base (r i)=true) ↔ ∃ j∈F,base j=true := by
    simp only [F,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨i,hi,hb⟩; exact ⟨r i,⟨i,hi,rfl⟩,hb⟩
    · rintro ⟨j,⟨i,hi,rfl⟩,hb⟩; exact ⟨i,hi,hb⟩
  have hF : F.card≤n := (Finset.card_image_le).trans (by simp)
  have hFr : ∑ j∈F,2*p j = t*F.card := by
    calc
      _ = ∑ _j∈F,t := Finset.sum_congr rfl (by
        intro j hj
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
        rw [hrate i (Finset.mem_range.mp hi)]
        ring)
      _ = _ := by simp [mul_comm]
  have hq := layer_nonquiet_bound s a b P p hp F
  rw [hFr] at hq
  have hqn : (∑ base,if ∃ j∈F,base j=true then layerMass s a b P p base else 0)≤t*n := by
    exact hq.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hF) ht)
  have hh := mul_le_mul_of_nonneg_right hqn (show 0≤t*(n:ℝ) by positivity)
  rw [Finset.sum_mul] at hh
  calc
    _ = ∑ base,(if ∃ j∈F,base j=true then layerMass s a b P p base else 0)*(t*n) := by
      apply Finset.sum_congr rfl
      intro base _
      simp only [he base]
      split_ifs <;> ring
    _ ≤ t*n*(t*n) := hh
    _ = _ := by ring

omit [Fintype T] in
lemma exposedSweep_coins (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p q : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hpq : ∀ i,i<n → p (r i)=q (r i)) (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r n v=exposedSweep s a b base P I q r n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [exposedSweep,exposedSweep,ih (fun i hi => hpq i (by omega))]
    simp only [exposedStep,hpq n (by omega)]

end Heisenberg.Exposure

open scoped Classical
namespace Heisenberg.Geometry

lemma reach_refl {d : ℕ} (U : Set (Site d)) (x : Site d) : Reach U x x :=
  Relation.ReflTransGen.refl

lemma reach_trans {d : ℕ} {U : Set (Site d)} {x y z : Site d}
    (hxy : Reach U x y) (hyz : Reach U y z) : Reach U x z := hxy.trans hyz

lemma reach_symm {d : ℕ} {U : Set (Site d)} {x y : Site d}
    (hxy : Reach U x y) : Reach U y x := by
  induction hxy with
  | refl => exact reach_refl U x
  | @tail b c hab hbc ih =>
    exact (Relation.ReflTransGen.single ⟨step_symm hbc.1, hbc.2.2, hbc.2.1⟩).trans ih

lemma reach_mono {d : ℕ} {U W : Set (Site d)} {x y : Site d}
    (hUW : U ⊆ W) (hxy : Reach U x y) : Reach W x y :=
  Relation.ReflTransGen.mono (fun _ _ h => ⟨h.1, hUW h.2.1, hUW h.2.2⟩) x y hxy

lemma step_update_succ {d : ℕ} (x : Site d) (j : Fin d) (a : ℤ) :
    Step (Function.update x j a) (Function.update x j (a + 1)) := by
  refine ⟨j, Or.inl ?_, ?_⟩
  · simp
  · intro k hk
    simp [Function.update_of_ne hk]

lemma reach_axis_nat {d : ℕ} (U : Set (Site d)) (x : Site d) (j : Fin d)
    (a : ℤ) (n : ℕ) (hU : ∀ k : ℕ, k ≤ n → Function.update x j (a + k) ∈ U) :
    Reach U (Function.update x j a) (Function.update x j (a + n)) := by
  induction n with
  | zero => simpa using reach_refl U (Function.update x j a)
  | succ n ih =>
    apply reach_trans (ih (fun k hk => hU k (by omega)))
    apply Relation.ReflTransGen.single
    refine ⟨?_, hU n (by omega), hU (n + 1) le_rfl⟩
    simpa [Nat.cast_add, Nat.cast_one, add_assoc] using step_update_succ x j (a + n)

lemma reach_axis {d : ℕ} (U : Set (Site d)) (x : Site d) (j : Fin d)
    (a b : ℤ) (hU : ∀ t, min a b ≤ t → t ≤ max a b → Function.update x j t ∈ U) :
    Reach U (Function.update x j a) (Function.update x j b) := by
  wlog hab : a ≤ b generalizing a b
  · exact reach_symm (this b a (by simpa [min_comm, max_comm] using hU) (by omega))
  have he : a + ((b - a).toNat : ℤ) = b := by omega
  rw [← he]
  apply reach_axis_nat
  intro k hk
  apply hU
  · simp only [min_eq_left hab]; omega
  · simp only [max_eq_right hab]; omega

end Heisenberg.Geometry

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticePaths
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma reach_rectangle {d : ℕ} (U : Set (Site d)) (x y : Site d)
    (hU : ∀ z, (∀ j, min (x j) (y j) ≤ z j ∧ z j ≤ max (x j) (y j)) → z ∈ U) :
    Reach U x y := by
  let v (s : Finset (Fin d)) : Site d := fun j => if j ∈ s then y j else x j
  have hv : ∀ s : Finset (Fin d), Reach U x (v s) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa [v] using reach_refl U x
    | @insert j s hj ih =>
      apply reach_trans ih
      have hstart : Function.update (v s) j (x j) = v s := by
        apply Function.update_eq_self_iff.mpr
        simp [v, hj]
      have hend : Function.update (v s) j (y j) = v (insert j s) := by
        funext k
        by_cases hk : k = j
        · subst k; simp [v]
        · simp [v, hk]
      rw [← hstart, ← hend]
      apply reach_axis
      intro t ht₁ ht₂
      apply hU
      intro k
      by_cases hk : k = j
      · subst k; simpa using And.intro ht₁ ht₂
      · simp only [Function.update_of_ne hk, v]
        split_ifs
        · exact ⟨min_le_right .., le_max_right ..⟩
        · exact ⟨min_le_left .., le_max_left ..⟩
  simpa [v] using hv Finset.univ

lemma shell_to_corner {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (x : Site d) (hx : x ∈ Shell r) :
    Reach (Shell r) x (fun _ => r) := by
  obtain ⟨hbox, j, hj⟩ := hx
  let y : Site d := fun k => if k = j then x j else r
  have hy : Reach (Shell r) x y := by
    apply reach_rectangle
    intro z hz
    refine ⟨?_, j, ?_⟩
    · intro k
      have h := hz k
      have hbound := hbox k
      have hybound : |y k| ≤ r := by
        dsimp [y]; split_ifs
        · exact hbox j
        · simp only [abs_of_nonneg hr, le_refl]
      rw [abs_le] at hbound hybound ⊢
      exact ⟨le_trans (le_min hbound.1 hybound.1) h.1,
        le_trans h.2 (max_le hbound.2 hybound.2)⟩
    · have h := hz j
      have hzj : z j = x j := by
        simp only [y, ite_eq_left rfl, min_self, max_self] at h
        exact le_antisymm h.2 h.1
      simpa [hzj] using hj
  obtain ⟨k, hkj⟩ : ∃ k : Fin d, k ≠ j := by
    have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    exact exists_ne j
  apply reach_trans hy
  have hstart : Function.update y j (x j) = y := by
    apply Function.update_eq_self_iff.mpr
    simp [y]
  have hend : Function.update y j r = (fun _ => r) := by
    funext a
    by_cases ha : a = j
    · subst a; simp
    · simp [y, ha]
  rw [← hstart, ← hend]
  apply reach_axis
  intro t ht₁ ht₂
  refine ⟨?_, k, ?_⟩
  · intro a
    by_cases ha : a = j
    · subst a
      simp only [Function.update_self]
      rw [abs_le]
      have hb := (abs_le.mp (hbox j))
      exact ⟨le_trans (le_min hb.1 (by omega)) ht₁,
        le_trans ht₂ (max_le hb.2 le_rfl)⟩
    · simp [y, ha, abs_of_nonneg hr]
  · simp [y, hkj, abs_of_nonneg hr]

lemma shell_connected {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (x y : Site d) (hx : x ∈ Shell r) (hy : y ∈ Shell r) :
    Reach (Shell r) x y :=
  reach_trans (shell_to_corner hd r hr x hx) (reach_symm (shell_to_corner hd r hr y hy))


lemma ray_unique {d : ℕ} (x z : Site d) (q q' : Direction d)
    (h : Ray x q z) (h' : Ray x q' z) : q = q' := by
  have hne : z q.1 ≠ x q.1 := by
    have hlt := h.1
    cases hb : q.2 <;> simp only [hb, Bool.false_eq_true, ↓reduceIte] at hlt
    · exact ne_of_lt hlt
    · exact ne_of_gt hlt
  have hj : q.1 = q'.1 := by
    by_contra hn
    exact hne (h'.2 q.1 hn)
  apply Prod.ext hj
  have h₁ := h.1
  have h₂ := h'.1
  rw [← hj] at h₂
  cases hb : q.2 <;> cases hb' : q'.2 <;>
    simp only [hb, hb', Bool.false_eq_true, ↓reduceIte] at h₁ h₂ ⊢ <;> omega

lemma exists_clear_ray {d : ℕ} (x : Site d) (F : Finset (Site d))
    (hF : F.card < 2 * d) : ∃ q : Direction d, ∀ z ∈ F, ¬ Ray x q z := by
  by_contra hn
  push Not at hn
  choose z hzF hz using hn
  let f : Direction d → F := fun q => ⟨z q, hzF q⟩
  have hf : Function.Injective f := by
    intro q q' he
    have hzEq : z q = z q' := congrArg Subtype.val he
    exact ray_unique x (z q) q q' (hz q) (hzEq ▸ hz q')
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool,
    Fintype.card_coe] at hc
  omega

lemma shell_radius_unique {d : ℕ} (x : Site d) (r t : ℤ)
    (hr : x ∈ Shell r) (ht : x ∈ Shell t) : r = t := by
  obtain ⟨hrbox, j, hj⟩ := hr
  obtain ⟨htbox, k, hk⟩ := ht
  exact le_antisymm (hj ▸ htbox j) (hk ▸ hrbox k)

lemma exists_clean_shell {d : ℕ} (K : ℤ) (F : Finset (Site d))
    (hF : F.card < 2 * d) :
    ∃ r : ℤ, K < r ∧ r ≤ K + 2 * d ∧ ∀ z ∈ F, z ∉ Shell r := by
  by_contra hn
  have hbad : ∀ n : Fin (2 * d), ∃ z ∈ F, z ∈ Shell (K + 1 + n.val) := by
    intro n
    have hl : K < K + 1 + (n.val : ℤ) := by omega
    have hu : K + 1 + (n.val : ℤ) ≤ K + 2 * d := by omega
    by_contra hn'
    push Not at hn'
    exact hn ⟨K + 1 + n.val, hl, hu, hn'⟩
  choose z hzF hz using hbad
  let f : Fin (2 * d) → F := fun n => ⟨z n, hzF n⟩
  have hf : Function.Injective f := by
    intro n n' he
    have hzEq : z n = z n' := congrArg Subtype.val he
    have hn := shell_radius_unique (z n) _ _ (hz n) (hzEq ▸ hz n')
    apply Fin.ext
    omega
  have hc := Fintype.card_le_of_injective f hf
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  omega

lemma reach_shell {d : ℕ} (r : ℤ) (hr : 0 ≤ r) (x : Site d)
    (hx : x ∈ Box r) (F : Finset (Site d)) (hxF : x ∉ F) (hF : F.card < 2 * d) :
    ∃ y ∈ Shell r, Reach (Box r \ (F : Set (Site d))) x y := by
  obtain ⟨q, hq⟩ := exists_clear_ray x F hF
  let b : ℤ := if q.2 then r else -r
  let y := Function.update x q.1 b
  have hb : |b| = r := by
    dsimp [b]; split_ifs <;> simp [abs_of_nonneg hr]
  have hybox : y ∈ Box r := by
    intro k
    by_cases hk : k = q.1
    · subst k; simpa [y] using hb.le
    · simpa [y, hk] using hx k
  have hyshell : y ∈ Shell r := ⟨hybox, q.1, by simpa [y] using hb⟩
  refine ⟨y, hyshell, ?_⟩
  have hstart := Function.update_eq_self q.1 x
  rw [← hstart]
  apply reach_axis
  intro t ht₁ ht₂
  constructor
  · intro k
    by_cases hk : k = q.1
    · subst k
      simp only [Function.update_self]
      rw [abs_le]
      have ha := abs_le.mp (hx q.1)
      have hb' := abs_le.mp hb.le
      exact ⟨le_trans (le_min ha.1 hb'.1) ht₁,
        le_trans ht₂ (max_le ha.2 hb'.2)⟩
    · simpa [hk] using hx k
  · intro htF
    by_cases ht : t = x q.1
    · subst t
      exact hxF (by simpa using htF)
    · apply hq (Function.update x q.1 t) htF
      refine ⟨?_, ?_⟩
      · simp only [Function.update_self]
        cases hq₂ : q.2
        · have hb' : b = -r := by simp [b, hq₂]
          have ha := abs_le.mp (hx q.1)
          simp only [Bool.false_eq_true, ↓reduceIte]
          have htmax : max (x q.1) b = x q.1 := max_eq_left (by omega)
          rw [htmax] at ht₂
          omega
        · have hb' : b = r := by simp [b, hq₂]
          have ha := abs_le.mp (hx q.1)
          simp only [↓reduceIte]
          have htmin : min (x q.1) b = x q.1 := min_eq_left (by omega)
          rw [htmin] at ht₁
          omega
      · intro k hk
        simp [hk]


lemma box_mono {d : ℕ} {r t : ℤ} (h : r ≤ t) : (Box r : Set (Site d)) ⊆ Box t :=
  fun _ hx j => (hx j).trans h

theorem finite_obstacle_connection {d : ℕ} (hd : 2 ≤ d) (K : ℤ) (hK : 0 ≤ K)
    (x y : Site d) (hx : x ∈ Box K) (hy : y ∈ Box K) (F : Finset (Site d))
    (hxF : x ∉ F) (hyF : y ∉ F) (hF : F.card < 2 * d) :
    Reach (Box (K + 2 * d) \ (F : Set (Site d))) x y := by
  obtain ⟨r, hKr, hrK, hrF⟩ := exists_clean_shell K F hF
  have hr : 0 ≤ r := by omega
  obtain ⟨a, ha, hxa⟩ := reach_shell r hr x (box_mono hKr.le hx) F hxF hF
  obtain ⟨b, hb, hyb⟩ := reach_shell r hr y (box_mono hKr.le hy) F hyF hF
  have hab : Reach (Box r \ (F : Set (Site d))) a b := by
    apply reach_mono _ (shell_connected hd r hr a b ha hb)
    intro z hz
    exact ⟨hz.1, fun hzF => hrF z hzF hz⟩
  apply reach_mono _ (hxa.trans (hab.trans (reach_symm hyb)))
  intro z hz
  exact ⟨box_mono hrK hz.1, hz.2⟩

lemma reach_has_simple_path {d : ℕ} (U : Set (Site d)) (x y : Site d)
    (h : Reach U x y) : ∃ p : (latticeGraph U).Walk x y, p.IsPath := by
  apply SimpleGraph.Reachable.exists_isPath
  exact (SimpleGraph.reachable_iff_reflTransGen ..).mpr h

lemma card_boxFinset (d r : ℕ) : (boxFinset d r).card = (2 * r + 1) ^ d := by
  simp only [boxFinset, Fintype.card_piFinset, Int.card_Icc]
  have hc : ((r : ℤ) + 1 + (r : ℤ)).toNat = 2 * r + 1 := by omega
  simp [hc]

lemma path_support_mem {d : ℕ} (U : Set (Site d)) (x y : Site d)
    (hx : x ∈ U) (p : (latticeGraph U).Walk x y) : ∀ z ∈ p.support, z ∈ U := by
  induction p with
  | nil => simpa using hx
  | @cons a b c hab p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hx
    · exact ih hab.2.2 z hz

end Heisenberg.Geometry
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeCuts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma step_translate {d : ℕ} (u : Site d) {x y : Site d} (h : Step x y) :
    Step (u + x) (u + y) := by
  obtain ⟨j, hj, hk⟩ := h
  refine ⟨j, ?_, ?_⟩
  · simp only [Pi.add_apply]
    rcases hj with h | h
    · left; omega
    · right; omega
  · intro k hkj
    simp only [Pi.add_apply, hk k hkj]

lemma reach_translate {d : ℕ} (u : Site d) (U W : Set (Site d))
    (hUW : ∀ z ∈ U, u + z ∈ W) {x y : Site d} (h : Reach U x y) :
    Reach W (u + x) (u + y) := by
  induction h with
  | refl => exact reach_refl W (u + x)
  | @tail b c hbc hstep ih =>
    exact ih.tail ⟨step_translate u hstep.1, hUW b hstep.2.1, hUW c hstep.2.2⟩

lemma ballFinset_card (d r : ℕ) (u : Site d) :
    (ballFinset d r u).card = (2 * r + 1) ^ d := by
  rw [ballFinset, Finset.card_image_of_injective _ (add_right_injective u), card_boxFinset]

theorem local_connectivity {d : ℕ} (hd : 2 ≤ d) (K : ℕ) (hK : 1 ≤ K)
    (u v : Site d) (F : Set (Site d)) (hvu : v ∈ Ball K u)
    (huF : u ∉ F) (hvF : v ∉ F)
    (hF : ((ballFinset d (K + 2 * d) u).filter (· ∈ F)).card < 2 * d) :
    ∃ p : (latticeGraph (Ball (K + 2 * d) u \ F)).Walk u v,
      p.IsPath ∧ p.length ≤ (2 * (K + 2 * d) + 1) ^ d := by
  let C := (ballFinset d (K + 2 * d) u).filter (· ∈ F)
  let G := C.image (fun z => z - u)
  have hG : G.card < 2 * d := (Finset.card_image_le).trans_lt hF
  have hzero : (0 : Site d) ∉ G := by
    intro hz
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
    have hae : a = u := sub_eq_zero.mp he
    exact huF (hae ▸ (Finset.mem_filter.mp ha).2)
  have hvG : v - u ∉ G := by
    intro hz
    obtain ⟨a, ha, he⟩ := Finset.mem_image.mp hz
    have hae : a = v := sub_left_injective he
    exact hvF (hae ▸ (Finset.mem_filter.mp ha).2)
  have hzbox : (0 : Site d) ∈ Box K := by intro j; simp
  have hvbox : v - u ∈ Box K := hvu
  have hconn := finite_obstacle_connection hd K (by positivity) 0 (v - u)
    hzbox hvbox G hzero hvG hG
  have hball : Reach (Ball (K + 2 * d) u \ F) u v := by
    have h := reach_translate u (Box (K + 2 * d) \ (G : Set (Site d)))
      (Ball (K + 2 * d) u \ F) (fun z hz => ?_) hconn
    · have he : u + (v - u) = v := by abel
      simpa only [add_zero, he] using h
    · refine ⟨(translate_mem_ball ..).mpr hz.1, ?_⟩
      intro hzF
      apply hz.2
      apply Finset.mem_image.mpr
      refine ⟨u + z, Finset.mem_filter.mpr ⟨?_, hzF⟩, by abel⟩
      apply (mem_ballFinset ..).mpr
      simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
        (translate_mem_ball u z (K + 2 * d)).mpr hz.1
  obtain ⟨p, hp⟩ := reach_has_simple_path _ u v hball
  refine ⟨p, hp, ?_⟩
  have hsupport : p.support.toFinset ⊆ ballFinset d (K + 2 * d) u := by
    intro z hz
    apply (mem_ballFinset ..).mpr
    have hzU := path_support_mem (Ball (K + 2 * d) u \ F) u v
      ⟨by intro j; simp; positivity, huF⟩ p z (List.mem_toFinset.mp hz)
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using hzU.1
  have hc := Finset.card_le_card hsupport
  rw [List.toFinset_card_of_nodup hp.support_nodup, SimpleGraph.Walk.length_support,
    ballFinset_card] at hc
  omega

end Heisenberg.Geometry

namespace Heisenberg.LatticePotential
variable {A : Type*} [AddCommGroup A]

lemma integral_succ (f : ℤ → A) (z : ℤ) : integral f (z+1) = integral f z + f z := by
  cases z with
  | ofNat n =>
    change (∑ k ∈ Finset.range (n+1), f (k:ℤ)) = (∑ k ∈ Finset.range n, f (k:ℤ)) + f (n:ℤ)
    exact Finset.sum_range_succ (fun k => f (k:ℤ)) n
  | negSucc n =>
    cases n with
    | zero => simp [integral]
    | succ n =>
      change -(∑ k ∈ Finset.range (n+1), f (-(k:ℤ)-1)) =
        -(∑ k ∈ Finset.range (n+1+1), f (-(k:ℤ)-1)) + f (Int.negSucc (n+1))
      rw [Finset.sum_range_succ (fun k : ℕ => f (-(k:ℤ)-1)) (n+1)]
      have he : Int.negSucc (n+1) = -((n+1:ℕ):ℤ)-1 := by omega
      rw [he]
      abel

lemma integral_ext_zero (f g : ℤ → A) (h0 : f 0 = g 0)
    (h : ∀ z, f (z+1)-f z = g (z+1)-g z) : f = g := by
  funext z
  induction z using Int.induction_on with
  | zero => exact h0
  | succ z ih => have := h z; rw [ih] at this; simpa only [Nat.cast_add,Nat.cast_one] using sub_left_inj.mp this
  | pred z ih =>
    have he := h (-(z:ℤ)-1)
    simp only [sub_add_cancel] at he
    rw [ih] at he
    exact sub_right_inj.mp he

lemma integral_sub (f g : ℤ → A) (z : ℤ) :
    integral (fun k => f k-g k) z = integral f z-integral g z := by
  cases z <;> simp [integral,Finset.sum_sub_distrib]; abel

lemma integral_telescoping (f : ℤ → A) (z : ℤ) :
    integral (fun k => f (k+1)-f k) z = f z-f 0 := by
  have h := integral_ext_zero (integral (fun k => f (k+1)-f k)) (fun z => f z-f 0)
    (by simp) (fun k => by rw [integral_succ]; abel)
  exact congrFun h z

lemma shift_cons_zero {d : ℕ} (a : ℤ) (x : Site d) :
    shift (Fin.cons a x) 0 = Fin.cons (a+1) x := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j <;> simp [shift]

lemma shift_cons_succ {d : ℕ} (a : ℤ) (x : Site d) (i : Fin d) :
    shift (Fin.cons a x) i.succ = Fin.cons a (shift x i) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · simp [shift,Function.update_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · by_cases he : j = i
    · subst j; simp [shift]
    · simp [shift,he]

theorem exists_potential (d : ℕ) (F : Site d → Fin d → A) (hF : Closed F) :
    ∃ g : Site d → A, ∀ x i, g (shift x i)-g x = F x i := by
  induction d with
  | zero => exact ⟨fun _ => 0, fun _ i => Fin.elim0 i⟩
  | succ d ih =>
    let F₀ : Site d → Fin d → A := fun x i => F (Fin.cons 0 x) i.succ
    have h₀ : Closed F₀ := by
      intro x i j
      simpa only [F₀,shift_cons_succ] using hF (Fin.cons 0 x) i.succ j.succ
    obtain ⟨g₀,hg₀⟩ := ih F₀ h₀
    let g : Site (d+1) → A := fun x =>
      g₀ (Fin.tail x)+integral (fun k => F (Fin.cons k (Fin.tail x)) 0) (x 0)
    refine ⟨g,?_⟩
    intro x i
    have hx : x = Fin.cons (x 0) (Fin.tail x) := (Fin.cons_self_tail x).symm
    nth_rw 1 [hx]
    rw [hx]
    generalize x 0 = a
    generalize Fin.tail x = y
    refine Fin.cases ?_ (fun j => ?_) i
    · rw [shift_cons_zero]
      simp only [g,Fin.tail_cons,Fin.cons_zero,integral_succ]
      abel
    · rw [shift_cons_succ]
      simp only [g,Fin.tail_cons,Fin.cons_zero]
      have hdiff : (fun k => F (Fin.cons k (shift y j)) 0-F (Fin.cons k y) 0) =
          (fun k => F (Fin.cons (k+1) y) j.succ-F (Fin.cons k y) j.succ) := by
        funext k
        have hc := hF (Fin.cons k y) 0 j.succ
        rw [shift_cons_zero,shift_cons_succ] at hc
        apply sub_eq_sub_iff_add_eq_add.mpr
        simpa only [add_comm] using hc.symm
      have hent := integral_telescoping (fun k => F (Fin.cons k y) j.succ) a
      rw [← hdiff,integral_sub] at hent
      have hbase := hg₀ y j
      dsimp only [F₀] at hbase
      calc
        _ = (g₀ (shift y j)-g₀ y) +
            (integral (fun k => F (Fin.cons k (shift y j)) 0) a -
              integral (fun k => F (Fin.cons k y) 0) a) := by abel
        _ = _ := by rw [hbase,hent]; abel

end Heisenberg.LatticePotential

namespace Heisenberg.LatticeCut
open Heisenberg.LatticePotential

lemma cutReach_cut {d : ℕ} {H : Set (Site d)} {e f : Edge d} (he : Cut H e) (h : CutReach H e f) : Cut H f := by
  induction h with
  | refl => exact he
  | tail _ h _ => exact h.2.1

lemma cutReach_square {d : ℕ} {H : Set (Site d)} {e f f' : Edge d} {x : Site d} {i j : Fin d}
    (he : Cut H e) (h : CutReach H e f) (hf : f ∈ square x i j) (hf' : f' ∈ square x i j)
    (hc : Cut H f') (hij : i ≠ j) : CutReach H e f' := by
  exact h.tail ⟨cutReach_cut he h,hc,⟨x,i,j,hij,hf,hf'⟩⟩

lemma shift_comm {d : ℕ} (x : Site d) (i j : Fin d) : shift (shift x i) j = shift (shift x j) i := by
  by_cases hij : i = j
  · subst j; rfl
  funext k
  by_cases hki : k = i
  · subst k; simp [shift,Function.update_of_ne hij,Function.update_of_ne (Ne.symm hij)]
  by_cases hkj : k = j
  · subst k; simp [shift,Function.update_of_ne hij,Function.update_of_ne (Ne.symm hij)]
  simp [shift,Function.update_of_ne hki,Function.update_of_ne hkj]

lemma gradient_closed {d : ℕ} (H : Set (Site d)) (e : Edge d) (he : Cut H e) : Closed (gradient H e) := by
  intro x i j
  by_cases hij : i = j
  · subst j; rfl
  by_cases h : ∃ f ∈ square x i j, CutReach H e f
  · obtain ⟨f,hf,hr⟩ := h
    have hg : ∀ f' ∈ square x i j,
        gradient H e f'.1 f'.2 = color H (shift f'.1 f'.2)-color H f'.1 := by
      intro f' hf'
      by_cases hc : Cut H f'
      · exact ite_eq_left (cutReach_square he hr hf hf' hc hij)
      · have hs : color H (shift f'.1 f'.2)-color H f'.1 = 0 := by
          exact sub_eq_zero.mpr (not_not.mp hc).symm
        simp [gradient,hs]
    have h1 := hg (x,i) (by simp [square])
    have h2 := hg (shift x i,j) (by simp [square])
    have h3 := hg (x,j) (by simp [square])
    have h4 := hg (shift x j,i) (by simp [square])
    rw [h1,h2,h3,h4]
    dsimp only
    rw [shift_comm x i j]
    omega
  · have hg : ∀ f ∈ square x i j, gradient H e f.1 f.2 = 0 := by
      intro f hf
      exact ite_eq_right (fun hr => h ⟨f,hf,hr⟩)
    rw [hg (x,i) (by simp [square]),hg (shift x i,j) (by simp [square]),
      hg (x,j) (by simp [square]),hg (shift x j,i) (by simp [square])]

lemma step_shift {d : ℕ} {x y : Site d} (h : Heisenberg.Geometry.Step x y) :
    (∃ i, y = shift x i) ∨ (∃ i, x = shift y i) := by
  obtain ⟨i,hi,hother⟩ := h
  rcases hi with hi | hi
  · left
    refine ⟨i,?_⟩
    funext j
    by_cases hji : j = i
    · subst j; simpa [shift] using hi
    · simpa [shift,Function.update_of_ne hji] using hother j hji
  · right
    refine ⟨i,?_⟩
    funext j
    by_cases hji : j = i
    · subst j; simpa [shift] using hi
    · simpa [shift,Function.update_of_ne hji] using (hother j hji).symm

lemma potential_constant {d : ℕ} (H : Set (Site d)) (e : Edge d) (g : Site d → ℤ)
    (hg : ∀ x i, g (shift x i)-g x = gradient H e x i) {U : Set (Site d)}
    (hU : ∀ x ∈ U, ∀ y ∈ U, color H x = color H y)
    {x y : Site d} (h : Heisenberg.Geometry.Reach U x y) : g x = g y := by
  induction h with
  | refl => rfl
  | @tail a b hab hstep ih =>
    have hcol := hU a hstep.2.1 b hstep.2.2
    have he : g a = g b := by
      rcases step_shift hstep.1 with ⟨j,rfl⟩ | ⟨j,rfl⟩
      · have hb := hg a j
        simp only [gradient,← hcol,sub_self,ite_self] at hb
        omega
      · have hb := hg b j
        simp only [gradient,hcol,sub_self,ite_self] at hb
        omega
    exact ih.trans he

theorem cut_connected {d : ℕ} (H : Set (Site d)) (hH : Connected H) (hU : Connected Hᶜ)
    (e f : Edge d) (he : Cut H e) (hf : Cut H f) : CutReach H e f := by
  obtain ⟨g,hg⟩ := exists_potential d (gradient H e) (gradient_closed H e he)
  have hconst : ∀ x y, (x ∈ H ↔ y ∈ H) → g x = g y := by
    intro x y hxy
    by_cases hx : x ∈ H
    · apply potential_constant H e g hg (U := H) (fun z hz w hw => by simp [color,hz,hw])
      exact hH x hx y (hxy.mp hx)
    · have hy : y ∈ Hᶜ := fun hy => hx (hxy.mpr hy)
      apply potential_constant H e g hg (U := Hᶜ) (fun z hz w hw => by simp [color, show z ∉ H from hz, show w ∉ H from hw])
      exact hU x hx y hy
  by_contra hn
  have hf0 := hg f.1 f.2
  simp only [gradient,ite_eq_right hn] at hf0
  have her : CutReach H e e := Relation.ReflTransGen.refl
  have he1 := hg e.1 e.2
  simp only [gradient,ite_eq_left her] at he1
  unfold Cut color at he hf
  by_cases heH : e.1 ∈ H <;> by_cases heH' : shift e.1 e.2 ∈ H <;>
    by_cases hfH : f.1 ∈ H <;> by_cases hfH' : shift f.1 f.2 ∈ H <;>
    simp only [heH,heH',hfH,hfH',↓reduceIte,ne_eq] at he hf
  all_goals try contradiction
  all_goals
    simp only [color,heH,heH',↓reduceIte] at he1
    have ha := hconst e.1 (if e.1 ∈ H ↔ f.1 ∈ H then f.1 else shift f.1 f.2)
      (by split_ifs <;> simp_all)
    have hb := hconst (shift e.1 e.2) (if shift e.1 e.2 ∈ H ↔ f.1 ∈ H then f.1 else shift f.1 f.2)
      (by split_ifs <;> simp_all)
    simp only [heH,heH',hfH,iff_self,true_iff,false_iff,not_true_eq_false,↓reduceIte] at ha hb
    omega

end Heisenberg.LatticeCut
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeHulls
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.Geometry

lemma exists_box {d : ℕ} (x : Site d) : ∃ r : ℕ, x ∈ Box (r : ℤ) := by
  refine ⟨Finset.univ.sup (fun i => (x i).natAbs),?_⟩
  intro j
  rw [← Int.natCast_natAbs]
  exact_mod_cast (Finset.le_sup (f := fun i => (x i).natAbs) (Finset.mem_univ j))

lemma exterior_to_shell {d : ℕ} (r R : ℤ) (hr : 0 ≤ r) (hR : r < R)
    (x : Site d) (hx : x ∉ Box r) (hxR : x ∈ Box R) :
    ∃ y ∈ Shell R, Reach (Box r)ᶜ x y := by
  obtain ⟨j,hj⟩ : ∃ j, r < |x j| := by
    simpa only [Box,Set.mem_ofPred_eq,not_forall,not_le] using hx
  let b : ℤ := if 0 ≤ x j then R else -R
  let y := Function.update x j b
  have hb : |b| = R := by
    dsimp [b]
    split_ifs <;> simp [abs_of_nonneg (by omega : 0 ≤ R)]
  have hy : y ∈ Shell R := by
    refine ⟨?_,j,?_⟩
    · intro k
      by_cases hk : k = j
      · subst k; simpa [y] using hb.le
      · simpa [y,hk] using hxR k
    · simpa [y] using hb
  refine ⟨y,hy,?_⟩
  rw [← Function.update_eq_self j x]
  apply reach_axis
  intro t ht₁ ht₂ ht
  have htj : |t| ≤ r := by simpa using ht j
  have hbound := abs_le.mp (hxR j)
  have htbound := abs_le.mp htj
  by_cases h : 0 ≤ x j
  · have hb' : b = R := ite_eq_left h
    rw [hb',min_eq_left hbound.2] at ht₁
    rw [abs_of_nonneg h] at hj
    omega
  · have hb' : b = -R := ite_eq_right h
    rw [hb',max_eq_left hbound.1] at ht₂
    rw [abs_of_neg (by omega)] at hj
    omega

lemma exterior_connected {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (x y : Site d) (hx : x ∉ Box r) (hy : y ∉ Box r) :
    Reach (Box r)ᶜ x y := by
  obtain ⟨a,ha⟩ := exists_box x
  obtain ⟨b,hb⟩ := exists_box y
  let R : ℤ := max (max a b) (r+1)
  have hR : r < R := by have := le_max_right (max (a:ℤ) b) (r+1); dsimp [R]; omega
  have haR : (a:ℤ) ≤ R := (le_max_left _ _).trans (le_max_left _ _)
  have hbR : (b:ℤ) ≤ R := (le_max_right _ _).trans (le_max_left _ _)
  obtain ⟨v,hv,hxv⟩ := exterior_to_shell r R hr hR x hx (box_mono haR ha)
  obtain ⟨w,hw,hyw⟩ := exterior_to_shell r R hr hR y hy (box_mono hbR hb)
  have hvw : Reach (Box r)ᶜ v w := by
    apply reach_mono _ (shell_connected hd R (by omega) v w hv hw)
    intro z hz hzr
    obtain ⟨j,hj⟩ := hz.2
    have := hzr j
    omega
  exact hxv.trans (hvw.trans (reach_symm hyw))

lemma reach_end_mem {d : ℕ} {U : Set (Site d)} {x y : Site d}
    (hx : x ∈ U) (h : Reach U x y) : y ∈ U := by
  induction h with
  | refl => exact hx
  | tail _ h _ => exact h.2.2

lemma ambient_connected {d : ℕ} (x y : Site d) : Reach Set.univ x y :=
  reach_rectangle Set.univ x y (by simp)

end Heisenberg.Geometry

namespace Heisenberg.LatticeHull
open Heisenberg.Geometry

lemma subset_hull {d : ℕ} (A : Set (Site d)) {b : Site d} (hb : b ∉ A) : A ⊆ Hull A b := by
  intro x hx hr
  exact reach_end_mem hb hr hx

lemma complement_connected {d : ℕ} (A : Set (Site d)) (b : Site d) :
    Heisenberg.LatticeCut.Connected (Hull A b)ᶜ := by
  intro x hx y hy
  have hx' : Reach Aᶜ b x := not_not.mp hx
  have hy' : Reach Aᶜ b y := not_not.mp hy
  have hr : Reach Aᶜ x y := (reach_symm hx').trans hy'
  induction hr with
  | refl => exact reach_refl _ _
  | @tail z w hz hw ih =>
    have hz' : Reach Aᶜ b z := hx'.trans hz
    exact (ih (not_not.mpr hz') hz').tail ⟨hw.1,not_not.mpr hz',not_not.mpr (hz'.tail hw)⟩

lemma inner_endpoint_mem {d : ℕ} (A : Set (Site d)) {b : Site d} (hb : b ∉ A)
    {x y : Site d} (hx : x ∈ Hull A b) (hy : y ∉ Hull A b) (hxy : Step x y) : x ∈ A := by
  by_contra h
  have hy' : Reach Aᶜ b y := not_not.mp hy
  exact hx (hy'.tail ⟨step_symm hxy,reach_end_mem hb hy',h⟩)

lemma hull_connected {d : ℕ} (A : Set (Site d)) (hA : Heisenberg.LatticeCut.Connected A)
    (hAn : A.Nonempty) {b : Site d} (hb : b ∉ A) :
    Heisenberg.LatticeCut.Connected (Hull A b) := by
  obtain ⟨a,ha⟩ := hAn
  have hAH := subset_hull A hb
  have hAll : ∀ x, x ∉ Hull A b ∨ Reach (Hull A b) a x := by
    intro x
    have hr := ambient_connected a x
    induction hr with
    | refl => exact Or.inr (reach_refl _ _)
    | @tail z w _ hzw ih =>
      by_cases hw : w ∈ Hull A b
      · right
        rcases ih with hz | hz
        · have hwA := inner_endpoint_mem A hb hw hz (step_symm hzw.1)
          exact reach_mono hAH (hA a ha w hwA)
        · exact hz.tail ⟨hzw.1,reach_end_mem (hAH ha) hz,hw⟩
      · exact Or.inl hw
  intro x hx y hy
  exact (reach_symm ((hAll x).resolve_left (fun h => h hx))).trans
    ((hAll y).resolve_left (fun h => h hy))

lemma finite_contained_box {d : ℕ} (A : Set (Site d)) (hA : A.Finite) :
    ∃ r : ℕ, A ⊆ Box (r : ℤ) := by
  have hx : ∀ x ∈ A, ∃ r : ℕ, x ∈ Box (r : ℤ) := fun x _ => exists_box x
  choose r hr using hx
  let R := hA.toFinset.sup (fun x => if h : x ∈ A then r x h else 0)
  refine ⟨R,?_⟩
  intro x hx
  apply box_mono _ (hr x hx)
  have hle : r x hx ≤ R := by
    simpa only [dite_eq_left hx] using Finset.le_sup (f := fun x => if h : x ∈ A then r x h else 0)
      (hA.mem_toFinset.mpr hx)
  exact_mod_cast hle

lemma reach_preserves_hull {d : ℕ} (A : Set (Site d)) (b : Site d) {x y : Site d}
    (hxy : Reach Aᶜ x y) : x ∈ Hull A b ↔ y ∈ Hull A b := by
  constructor
  · intro hx hy
    exact hx (hy.trans (reach_symm hxy))
  · intro hy hx
    exact hy (hx.trans hxy)

lemma connected_avoids_hull {d : ℕ} (A V : Set (Site d)) (b : Site d)
    (hV : Heisenberg.LatticeCut.Connected V) (hVA : Disjoint V A)
    {x : Site d} (hx : x ∈ V) (hxH : x ∉ Hull A b) : V ⊆ (Hull A b)ᶜ := by
  intro y hy hyH
  apply hxH
  apply (reach_preserves_hull A b ?_).mpr hyH
  apply reach_mono _ (hV x hx y hy)
  intro z hz hzA
  exact Set.disjoint_left.mp hVA hz hzA

lemma hull_subset_of_subset_hull {d : ℕ} (A B : Set (Site d)) (b : Site d)
    (hAB : A ⊆ Hull B b) : Hull A b ⊆ Hull B b := by
  intro x hx
  by_contra hxB
  apply hx
  have hb : b ∈ (Hull B b)ᶜ := fun h => h (reach_refl Bᶜ b)
  have hbx := complement_connected B b b hb x hxB
  apply reach_mono _ hbx
  intro z hz hzA
  exact hz (hAB hzA)

theorem hull_laminar {d : ℕ} (A B : Set (Site d))
    (hA : Heisenberg.LatticeCut.Connected A) (hB : Heisenberg.LatticeCut.Connected B)
    (hAn : A.Nonempty) (_hBn : B.Nonempty) (hAB : Disjoint A B)
    {b : Site d} (hbA : b ∉ A) (_hbB : b ∉ B) :
    Hull A b ⊆ Hull B b ∨ Hull B b ⊆ Hull A b ∨ Disjoint (Hull A b) (Hull B b) := by
  by_cases hsubA : A ⊆ Hull B b
  · exact Or.inl (hull_subset_of_subset_hull A B b hsubA)
  by_cases hsubB : B ⊆ Hull A b
  · exact Or.inr (Or.inl (hull_subset_of_subset_hull B A b hsubB))
  obtain ⟨a,ha,haB⟩ : ∃ a ∈ A, a ∉ Hull B b := Set.not_subset.mp hsubA
  obtain ⟨c,hc,hcA⟩ : ∃ c ∈ B, c ∉ Hull A b := Set.not_subset.mp hsubB
  have hBext := connected_avoids_hull A B b hB hAB.symm hc hcA
  have hHB : Disjoint (Hull A b) B := Set.disjoint_left.mpr (fun x hx hxB => hBext hxB hx)
  have hHAext := connected_avoids_hull B (Hull A b) b (hull_connected A hA hAn hbA)
    hHB (subset_hull A hbA ha) haB
  exact Or.inr (Or.inr (Set.disjoint_left.mpr (fun x hx hxB => hHAext hx hxB)))

end Heisenberg.LatticeHull
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HullComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical

namespace Heisenberg.LatticeCut
open Heisenberg.Geometry
open Heisenberg.LatticePotential (shift)

lemma step_to_shift {d : ℕ} (x : Site d) (i : Fin d) : Step x (shift x i) := by
  refine ⟨i,Or.inl ?_,?_⟩
  · simp [shift]
  · intro k hk; simp [shift,hk]

lemma cut_mem_iff {d : ℕ} (H : Set (Site d)) (e : Edge d) :
    Cut H e ↔ (e.1 ∈ H ∧ shift e.1 e.2 ∉ H) ∨ (e.1 ∉ H ∧ shift e.1 e.2 ∈ H) := by
  by_cases h : e.1 ∈ H <;> by_cases h' : shift e.1 e.2 ∈ H <;> simp [Cut,color,h,h']

lemma outer_boundary {d : ℕ} (H : Set (Site d)) (e : Edge d) (he : Cut H e) :
    outer H e ∈ Boundary H := by
  rcases (cut_mem_iff H e).mp he with ⟨h,h'⟩ | ⟨h,h'⟩
  · rw [outer,ite_eq_left h]
    exact ⟨h',e.1,h,step_to_shift e.1 e.2⟩
  · rw [outer,ite_eq_right h]
    exact ⟨h,shift e.1 e.2,h',step_symm (step_to_shift e.1 e.2)⟩

lemma boundary_has_cut {d : ℕ} (H : Set (Site d)) (v : Site d) (hv : v ∈ Boundary H) :
    ∃ e, Cut H e ∧ outer H e = v := by
  obtain ⟨hv,u,hu,huv⟩ := hv
  rcases step_shift huv with ⟨i,rfl⟩ | ⟨i,rfl⟩
  · exact ⟨(u,i),(cut_mem_iff ..).mpr (Or.inl ⟨hu,hv⟩),by simp [outer,hu]⟩
  · exact ⟨(v,i),(cut_mem_iff ..).mpr (Or.inr ⟨hv,hu⟩),by simp [outer,hv]⟩

lemma square_outer_bounds {d : ℕ} (H : Set (Site d)) {x : Site d} {i j : Fin d}
    (hij : i ≠ j) {e : Edge d} (he : e ∈ square x i j) (k : Fin d) :
    x k ≤ outer H e k ∧ outer H e k ≤ x k+1 := by
  simp only [square,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with rfl | rfl | rfl | rfl
  all_goals
    unfold outer
    split_ifs
    all_goals
      by_cases hki : k = i
      · subst k; simp [shift,hij,Ne.symm hij]
      · by_cases hkj : k = j
        · subst k; simp [shift,hij,Ne.symm hij]
        · simp [shift,hki,hkj]

lemma linked_outer_near {d : ℕ} (H : Set (Site d)) {e f : Edge d}
    (h : Linked H e f) : outer H f ∈ Ball 1 (outer H e) := by
  obtain ⟨_,_,x,i,j,hij,he,hf⟩ := h
  intro k
  have he' := square_outer_bounds H hij he k
  have hf' := square_outer_bounds H hij hf k
  rw [abs_le]
  omega

theorem boundary_connected {d : ℕ} (H : Set (Site d)) (hH : Connected H) (hU : Connected Hᶜ)
    (x y : Site d) (hx : x ∈ Boundary H) (hy : y ∈ Boundary H) :
    Relation.ReflTransGen (fun a b => b ∈ Ball 1 a ∧ a ∈ Boundary H ∧ b ∈ Boundary H) x y := by
  obtain ⟨e,he,rfl⟩ := boundary_has_cut H x hx
  obtain ⟨f,hf,rfl⟩ := boundary_has_cut H y hy
  have hr := cut_connected H hH hU e f he hf
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail g f hrg hgf ih =>
    exact (ih hgf.1 (outer_boundary H g hgf.1)).tail
      ⟨linked_outer_near H hgf,outer_boundary H g hgf.1,outer_boundary H f hgf.2.1⟩

end Heisenberg.LatticeCut

namespace Heisenberg.Geometry

lemma ball_symm {d : ℕ} {r : ℤ} {x y : Site d} (h : y ∈ Ball r x) : x ∈ Ball r y := by
  intro j
  simpa only [abs_sub_comm] using h j

lemma ball_triangle {d : ℕ} {r s : ℤ} {x y z : Site d}
    (hxy : y ∈ Ball r x) (hyz : z ∈ Ball s y) : z ∈ Ball (r+s) x := by
  intro j
  have h : z j-x j = (z j-y j)+(y j-x j) := by omega
  rw [h]
  exact (abs_add_le ..).trans (by have := hxy j; have := hyz j; omega)

lemma ball_mono {d : ℕ} {r s : ℤ} (h : r ≤ s) (x : Site d) : Ball r x ⊆ Ball s x :=
  fun _ hz j => (hz j).trans h

lemma ball_self {d : ℕ} {r : ℤ} (hr : 0 ≤ r) (x : Site d) : x ∈ Ball r x := by
  intro j; simpa using hr

lemma ball_connected {d : ℕ} (r : ℤ) (x : Site d) : Heisenberg.LatticeCut.Connected (Ball r x) := by
  intro y hy z hz
  apply reach_rectangle
  intro w hw j
  have hyj := abs_le.mp (hy j)
  have hzj := abs_le.mp (hz j)
  have hwj := hw j
  rw [abs_le]
  constructor <;> omega

end Heisenberg.Geometry

namespace Heisenberg.LatticeComponents
open Heisenberg.Geometry

lemma self_mem_component {d : ℕ} (Z : Set (Site d)) {x : Site d} (hx : x ∈ Z) : x ∈ Component Z x :=
  ⟨hx,Relation.ReflTransGen.refl⟩

lemma component_closed {d : ℕ} (Z : Set (Site d)) (x : Site d) {y z : Site d}
    (hy : y ∈ Component Z x) (hz : z ∈ Z) (hyz : z ∈ Ball 8 y) : z ∈ Component Z x :=
  ⟨hz,hy.2.tail ⟨hyz,hy.1,hz⟩⟩

lemma component_symmetric {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Component Z x) : x ∈ Component Z y := by
  refine ⟨hx,?_⟩
  have hr := hy.2
  induction hr with
  | refl => exact Relation.ReflTransGen.refl
  | @tail z w _ hzw ih =>
    exact (Relation.ReflTransGen.single ⟨ball_symm hzw.1,hzw.2.2,hzw.2.1⟩).trans (ih ⟨hzw.2.1,by assumption⟩)

lemma component_eq_of_mem {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Component Z x) : Component Z y = Component Z x := by
  have hyx := component_symmetric Z hx hy
  ext z
  exact ⟨fun hz => ⟨hz.1,hy.2.trans hz.2⟩,fun hz => ⟨hz.1,hyx.2.trans hz.2⟩⟩

lemma components_disjoint {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Z) (hne : Component Z x ≠ Component Z y) :
    Disjoint (Component Z x) (Component Z y) := by
  apply Set.disjoint_left.mpr
  intro z hzx hzy
  exact hne ((component_eq_of_mem Z hx hzx).symm.trans (component_eq_of_mem Z hy hzy))

lemma thickenings_disjoint {d : ℕ} (Z : Set (Site d)) {x y : Site d}
    (hx : x ∈ Z) (hy : y ∈ Z) (hne : Component Z x ≠ Component Z y) :
    Disjoint (Thick 4 (Component Z x)) (Thick 4 (Component Z y)) := by
  apply Set.disjoint_left.mpr
  rintro z ⟨u,hu,hzu⟩ ⟨v,hv,hzv⟩
  have huv : v ∈ Ball 8 u := by
    simpa using ball_triangle hzu (ball_symm hzv)
  have hvx := component_closed Z x hu hv.1 huv
  exact Set.disjoint_left.mp (components_disjoint Z hx hy hne) hvx hv

lemma overlapping_balls {d : ℕ} {x y : Site d} (hxy : y ∈ Ball 8 x) :
    ∃ z, z ∈ Ball 4 x ∧ z ∈ Ball 4 y := by
  refine ⟨fun j => max (x j-4) (y j-4),?_,?_⟩
  all_goals
    intro j
    have h := abs_le.mp (hxy j)
    dsimp only
    rw [abs_le]
    constructor <;> omega

lemma thick_component_connected {d : ℕ} (Z : Set (Site d)) {x : Site d} (_hx : x ∈ Z) :
    Heisenberg.LatticeCut.Connected (Thick 4 (Component Z x)) := by
  let A := Thick 4 (Component Z x)
  have hball : ∀ y ∈ Component Z x, Ball 4 y ⊆ A := fun y hy z hz => ⟨y,hy,hz⟩
  have hbase : ∀ y ∈ Component Z x, Reach A x y := by
    intro y hy
    have hr := hy.2
    induction hr with
    | refl => exact reach_refl _ _
    | @tail v w hvw hstep ih =>
      have hv : v ∈ Component Z x := ⟨hstep.2.1,hvw⟩
      have hw : w ∈ Component Z x := ⟨hstep.2.2,hvw.tail hstep⟩
      obtain ⟨z,hzv,hzw⟩ := overlapping_balls hstep.1
      exact (ih hv).trans ((reach_mono (hball v hv)
        (ball_connected 4 v v (ball_self (by omega) v) z hzv)).trans
        (reach_mono (hball w hw) (ball_connected 4 w z hzw w (ball_self (by omega) w))))
  have hAll : ∀ y ∈ A, Reach A x y := by
    rintro y ⟨z,hz,hyz⟩
    exact (hbase z hz).trans (reach_mono (hball z hz)
      (ball_connected 4 z z (ball_self (by omega) z) y hyz))
  intro y hy z hz
  exact (reach_symm (hAll y hy)).trans (hAll z hz)

lemma boundary_unit_clear {d : ℕ} (Z : Set (Site d)) {x b v : Site d}
    (hb : b ∉ Thick 4 (Component Z x))
    (hv : v ∈ Heisenberg.LatticeCut.Boundary (Heisenberg.LatticeHull.Hull (Thick 4 (Component Z x)) b)) :
    Ball 1 v ⊆ Zᶜ := by
  obtain ⟨hv,u,hu,huv⟩ := hv
  have huA := Heisenberg.LatticeHull.inner_endpoint_mem _ hb hu hv huv
  obtain ⟨c,hc,huc⟩ := huA
  have hvc : v ∈ Ball 5 c := by simpa using ball_triangle huc (step_ball_one huv)
  intro z hz hzZ
  have hzc : z ∈ Ball 8 c := ball_mono (by omega : (6:ℤ) ≤ 8) c (ball_triangle hvc hz)
  have hzC := component_closed Z x hc hzZ hzc
  have hvA : v ∈ Thick 4 (Component Z x) := ⟨z,hzC,ball_mono (by omega : (1:ℤ) ≤ 4) z (ball_symm hz)⟩
  exact hv (Heisenberg.LatticeHull.subset_hull _ hb hvA)

end Heisenberg.LatticeComponents

namespace Heisenberg.Geometry

lemma exterior_ball_connected {d : ℕ} (hd : 2 ≤ d) (r : ℤ) (hr : 0 ≤ r)
    (c x y : Site d) (hx : x ∉ Ball r c) (hy : y ∉ Ball r c) :
    Reach (Ball r c)ᶜ x y := by
  have hx' : x-c ∉ Box r := hx
  have hy' : y-c ∉ Box r := hy
  have hxy := exterior_connected hd r hr (x-c) (y-c) hx' hy'
  have h := reach_translate c (Box r)ᶜ (Ball r c)ᶜ (fun z hz hzc =>
    hz ((translate_mem_ball c z r).mp hzc)) hxy
  simpa only [add_sub_cancel] using h

lemma ball_finite {d : ℕ} (r : ℕ) (x : Site d) : (Ball (r : ℤ) x).Finite := by
  have he : Ball (r : ℤ) x = (ballFinset d r x : Set (Site d)) := by
    ext z; exact (mem_ballFinset ..).symm
  rw [he]
  exact Finset.finite_toSet _

lemma ball_enlarge_step {d : ℕ} {c u v : Site d} {r : ℤ}
    (hu : u ∈ Ball r c) (huv : Step u v) : v ∈ Ball (r+1) c :=
  ball_triangle hu (step_ball_one huv)

lemma interpolate_near_confined {d : ℕ} {U : Set (Site d)} {c x y : Site d} {r : ℤ}
    (hx : x ∈ Ball r c) (hy : y ∈ Ball r c)
    (hxy : y ∈ Ball 1 x) (hU : Ball 1 x ⊆ U) : Reach (Ball r c ∩ U) x y := by
  apply reach_rectangle
  intro z hz
  constructor
  · intro j
    have hxj := abs_le.mp (hx j)
    have hyj := abs_le.mp (hy j)
    have hzj := hz j
    rw [abs_le]
    constructor <;> omega
  · apply hU
    intro j
    have hyj := abs_le.mp (hxy j)
    have hzj := hz j
    rw [abs_le]
    constructor <;> omega

end Heisenberg.Geometry
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HullRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped Classical
namespace Heisenberg.LatticeHull
open Heisenberg.Geometry

lemma hull_subset_ball {d : ℕ} (hd : 2 ≤ d) (A : Set (Site d)) (c : Site d) (r : ℤ) (hr : 0 ≤ r)
    (hAr : A ⊆ Ball r c) {b : Site d} (hb : b ∉ Ball r c) : Hull A b ⊆ Ball r c := by
  intro x hx
  by_contra hxr
  apply hx
  apply reach_mono _ (exterior_ball_connected hd r hr c b x hb hxr)
  intro z hz hzA
  exact hz (hAr hzA)

lemma boundary_subset_ball {d : ℕ} (H : Set (Site d)) (c : Site d) (r : ℤ)
    (hH : H ⊆ Ball r c) : Heisenberg.LatticeCut.Boundary H ⊆ Ball (r+1) c := by
  rintro v ⟨_,u,hu,huv⟩
  exact ball_enlarge_step (hH hu) huv

lemma boundary_nonempty {d : ℕ} (H : Set (Site d)) {x y : Site d} (hx : x ∈ H) (hy : y ∉ H) :
    (Heisenberg.LatticeCut.Boundary H).Nonempty := by
  have hr := ambient_connected x y
  have h : y ∈ H ∨ (Heisenberg.LatticeCut.Boundary H).Nonempty := by
    clear hy
    induction hr with
    | refl => exact Or.inl hx
    | @tail u v _ huv ih =>
      rcases ih with hu | hu
      · by_cases hv : v ∈ H
        · exact Or.inl hv
        · exact Or.inr ⟨v,hv,u,hu,huv.1⟩
      · exact Or.inr hu
  exact h.resolve_left hy

end Heisenberg.LatticeHull
namespace Heisenberg.LatticeComponents
open Heisenberg.Geometry Heisenberg.LatticeHull

lemma thick_nonempty {d : ℕ} (Z : Set (Site d)) {x : Site d} (hx : x ∈ Z) :
    (Thick 4 (Component Z x)).Nonempty := ⟨x,x,self_mem_component Z hx,ball_self (by omega) x⟩

theorem surviving_boundary_confined {d : ℕ} (Z : Set (Site d)) {x b c : Site d}
    (hx : x ∈ Z) (hb : b ∉ Thick 4 (Component Z x)) (r : ℤ)
    (hH : Hull (Thick 4 (Component Z x)) b ⊆ Ball r c)
    (u v : Site d)
    (hu : u ∈ Heisenberg.LatticeCut.Boundary (Hull (Thick 4 (Component Z x)) b))
    (hv : v ∈ Heisenberg.LatticeCut.Boundary (Hull (Thick 4 (Component Z x)) b)) :
    Reach (Ball (r+1) c ∩ Zᶜ) u v := by
  have hB := boundary_subset_ball _ c r hH
  have hr := Heisenberg.LatticeCut.boundary_connected _
    (hull_connected _ (thick_component_connected Z hx) (thick_nonempty Z hx) hb)
    (complement_connected _ b) u v hu hv
  induction hr with
  | refl => exact reach_refl _ _
  | @tail w z _ hwz ih =>
    exact (ih hwz.2.1).trans (interpolate_near_confined (hB hwz.2.1) (hB hwz.2.2)
      hwz.1 (boundary_unit_clear Z hb hwz.2.1))

end Heisenberg.LatticeComponents

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents

variable {d : ℕ}

lemma member_unique {F : Finset (Set (Site d))} (hF : DisjointFamily F)
    {H K : Set (Site d)} (hH : H ∈ F) (hK : K ∈ F) {x : Site d}
    (hxH : x ∈ H) (hxK : x ∈ K) : H = K := by
  by_contra hne
  exact Set.disjoint_left.mp (hF H hH K hK hne) hxH hxK

lemma collapse_of_mem {F : Finset (Set (Site d))} (hF : DisjointFamily F)
    (rep : Set (Site d) → Site d) {H : Set (Site d)} (hH : H ∈ F) {x : Site d} (hx : x ∈ H) :
    collapse F rep x = rep H := by
  have h : ∃ K ∈ F, x ∈ K := ⟨H,hH,hx⟩
  rw [collapse,dite_eq_left h]
  rw [member_unique hF h.choose_spec.1 hH h.choose_spec.2 hx]

lemma collapse_free {F : Finset (Set (Site d))} (rep : Set (Site d) → Site d) {x : Site d}
    (hx : ¬ ∃ H ∈ F, x ∈ H) : collapse F rep x = x := by rw [collapse,dite_eq_right hx]

lemma collapse_survives (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (rep : Set (Site d) → Site d) (hcover : ∀ x ∈ Z, ∃ H ∈ F, x ∈ H)
    (hrep : ∀ H ∈ F, rep H ∉ Z) (x : Site d) : collapse F rep x ∉ Z := by
  unfold collapse
  split_ifs with h
  · exact hrep h.choose h.choose_spec.1
  · exact fun hx => h (hcover x hx)

lemma region_boundary (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (E : Set (Site d) → Set (Site d)) (u v : Site d)
    {H : Set (Site d)} (hH : H ∈ F) (hc : u ∈ H ∨ v ∈ H) :
    E H ∩ Zᶜ ⊆ RouteRegion Z F E u v := by
  exact fun z hz => ⟨Or.inr (Or.inr ⟨H,hH,hc,hz.1⟩),hz.2⟩

theorem route_exists (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (hF : DisjointFamily F) (rep : Set (Site d) → Site d)
    (E : Set (Site d) → Set (Site d))
    (hcover : ∀ x ∈ Z, ∃ H ∈ F, x ∈ H)
    (hroute : ∀ H ∈ F, ∀ v ∈ Boundary H, Reach (E H ∩ Zᶜ) (rep H) v)
    (hclear : ∀ H ∈ F, Boundary H ⊆ Zᶜ)
    {u v : Site d} (huv : Step u v) :
    Reach (RouteRegion Z F E u v) (collapse F rep u) (collapse F rep v) := by
  by_cases hu : ∃ H ∈ F, u ∈ H
  · obtain ⟨H,hH,huH⟩ := hu
    rw [collapse_of_mem hF rep hH huH]
    by_cases hv : ∃ K ∈ F, v ∈ K
    · obtain ⟨K,hK,hvK⟩ := hv
      rw [collapse_of_mem hF rep hK hvK]
      by_cases hHK : H = K
      · subst K; exact reach_refl _ _
      have hvH : v ∉ H := fun hvH => hHK (member_unique hF hH hK hvH hvK)
      have huK : u ∉ K := fun huK => hHK (member_unique hF hH hK huH huK)
      have hvB : v ∈ Boundary H := ⟨hvH,u,huH,huv⟩
      have huB : u ∈ Boundary K := ⟨huK,v,hvK,step_symm huv⟩
      have hru := reach_mono (region_boundary Z F E u v hH (Or.inl huH)) (hroute H hH v hvB)
      have hrv := reach_symm (reach_mono (region_boundary Z F E u v hK (Or.inr hvK))
        (hroute K hK u huB))
      exact hru.trans ((Relation.ReflTransGen.single ⟨step_symm huv,
        ⟨Or.inr (Or.inl rfl),hclear H hH hvB⟩,⟨Or.inl rfl,hclear K hK huB⟩⟩).trans hrv)
    · rw [collapse_free rep hv]
      have hvH : v ∉ H := fun hvH => hv ⟨H,hH,hvH⟩
      exact reach_mono (region_boundary Z F E u v hH (Or.inl huH))
        (hroute H hH v ⟨hvH,u,huH,huv⟩)
  · rw [collapse_free rep hu]
    by_cases hv : ∃ K ∈ F, v ∈ K
    · obtain ⟨K,hK,hvK⟩ := hv
      rw [collapse_of_mem hF rep hK hvK]
      have huK : u ∉ K := fun huK => hu ⟨K,hK,huK⟩
      exact reach_symm (reach_mono (region_boundary Z F E u v hK (Or.inr hvK))
        (hroute K hK u ⟨huK,v,hvK,step_symm huv⟩))
    · rw [collapse_free rep hv]
      exact Relation.ReflTransGen.single ⟨huv,
        ⟨Or.inl rfl,fun huZ => hu (hcover u huZ)⟩,
        ⟨Or.inr (Or.inl rfl),fun hvZ => hv (hcover v hvZ)⟩⟩

lemma mem_allHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) (H : Set (Site d)) :
    H ∈ allHulls Z hZ b ↔ ∃ x ∈ Z, Hull (Thick 4 (Component Z x)) b = H := by
  simp [allHulls]

lemma mem_maxHulls (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d) (H : Set (Site d)) :
    H ∈ maxHulls Z hZ b ↔ Maximal (· ∈ allHulls Z hZ b) H := by
  simp only [maxHulls,Finset.mem_filter]
  exact ⟨And.right,fun h => ⟨h.prop,h⟩⟩

lemma allHulls_laminar (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) {H K : Set (Site d)}
    (hH : H ∈ allHulls Z hZ b) (hK : K ∈ allHulls Z hZ b) :
    H ⊆ K ∨ K ⊆ H ∨ Disjoint H K := by
  obtain ⟨x,hx,rfl⟩ := (mem_allHulls Z hZ b H).mp hH
  obtain ⟨y,hy,rfl⟩ := (mem_allHulls Z hZ b K).mp hK
  by_cases he : Component Z x = Component Z y
  · exact Or.inl (by rw [he])
  have hbC : ∀ a, b ∉ Thick 4 (Component Z a) := by
    rintro a ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
  exact hull_laminar _ _ (thick_component_connected Z hx) (thick_component_connected Z hy)
    (thick_nonempty Z hx) (thick_nonempty Z hy) (thickenings_disjoint Z hx hy he) (hbC x) (hbC y)

lemma maxHulls_disjoint (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) : DisjointFamily (maxHulls Z hZ b) := by
  intro H hH K hK hne
  have hHm := (mem_maxHulls Z hZ b H).mp hH
  have hKm := (mem_maxHulls Z hZ b K).mp hK
  rcases allHulls_laminar Z hZ b hb hHm.prop hKm.prop with h | h | h
  · exact (hne (Set.Subset.antisymm h (hHm.le_of_ge hKm.prop h))).elim
  · exact (hne (Set.Subset.antisymm (hKm.le_of_ge hHm.prop h) h)).elim
  · exact h

lemma maxHulls_cover (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) (x : Site d) (hx : x ∈ Z) : ∃ H ∈ maxHulls Z hZ b, x ∈ H := by
  let H := Hull (Thick 4 (Component Z x)) b
  have hH : H ∈ allHulls Z hZ b := (mem_allHulls ..).mpr ⟨x,hx,rfl⟩
  obtain ⟨K,hHK,hK⟩ := (allHulls Z hZ b).exists_le_maximal hH
  refine ⟨K,(mem_maxHulls ..).mpr hK,hHK ?_⟩
  have hbC : b ∉ Thick 4 (Component Z x) := by
    rintro ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
  exact subset_hull _ hbC ⟨x,self_mem_component Z hx,ball_self (by omega) x⟩

lemma allHulls_boundary_nonempty (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) {H : Set (Site d)} (hH : H ∈ allHulls Z hZ b) :
    (Boundary H).Nonempty := by
  obtain ⟨x,hx,rfl⟩ := (mem_allHulls ..).mp hH
  have hbC : b ∉ Thick 4 (Component Z x) := by
    rintro ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
  apply boundary_nonempty _ (subset_hull _ hbC ⟨x,self_mem_component Z hx,ball_self (by omega) x⟩)
  exact fun h => h (reach_refl _ _)

theorem finite_hull_routing (Z : Set (Site d)) (hZ : Z.Finite) (b : Site d)
    (hb : b ∉ Thick 4 Z) :
    ∃ rep : Set (Site d) → Site d,
      (∀ H ∈ maxHulls Z hZ b, rep H ∈ Boundary H) ∧
      (∀ z, collapse (maxHulls Z hZ b) rep z ∉ Z) ∧
      ∀ (c : Set (Site d) → Site d) (r : Set (Site d) → ℤ),
        (∀ H ∈ maxHulls Z hZ b, H ⊆ Ball (r H) (c H)) →
        ∀ u v, Step u v →
        ∃ p : (latticeGraph (RouteRegion Z (maxHulls Z hZ b)
          (fun H => Ball (r H + 1) (c H)) u v)).Walk
            (collapse (maxHulls Z hZ b) rep u) (collapse (maxHulls Z hZ b) rep v), p.IsPath := by
  let F := maxHulls Z hZ b
  have hF := maxHulls_disjoint Z hZ b hb
  have hBn : ∀ H ∈ F, (Boundary H).Nonempty := fun H hH =>
    allHulls_boundary_nonempty Z hZ b hb ((mem_maxHulls ..).mp hH).prop
  let rep (H : Set (Site d)) : Site d := if h : H ∈ F then (hBn H h).choose else 0
  have hrB : ∀ H ∈ F, rep H ∈ Boundary H := by
    intro H hH
    simpa only [rep,dite_eq_left hH] using (hBn H hH).choose_spec
  have hclear : ∀ H ∈ F, Boundary H ⊆ Zᶜ := by
    intro H hH v hv
    obtain ⟨x,hx,rfl⟩ := (mem_allHulls ..).mp ((mem_maxHulls ..).mp hH).prop
    have hbC : b ∉ Thick 4 (Component Z x) := by
      rintro ⟨c,hc,hbc⟩; exact hb ⟨c,hc.1,hbc⟩
    exact boundary_unit_clear Z hbC hv (ball_self (by omega) v)
  refine ⟨rep,hrB,collapse_survives Z F rep (maxHulls_cover Z hZ b hb)
    (fun H hH => hclear H hH (hrB H hH)),?_⟩
  intro c r hbound u v huv
  apply reach_has_simple_path
  apply route_exists Z F hF rep _ (maxHulls_cover Z hZ b hb) _ hclear huv
  intro H hH w hw
  obtain ⟨x,hx,he⟩ := (mem_allHulls ..).mp ((mem_maxHulls ..).mp hH).prop
  have hbC : b ∉ Thick 4 (Component Z x) := by
    rintro ⟨a,ha,hba⟩; exact hb ⟨a,ha.1,hba⟩
  have hv : rep H ∈ Boundary (Hull (Thick 4 (Component Z x)) b) := by
    simpa only [he] using hrB H hH
  have hw' : w ∈ Boundary (Hull (Thick 4 (Component Z x)) b) := by
    simpa only [he] using hw
  have hB : Hull (Thick 4 (Component Z x)) b ⊆ Ball (r H) (c H) := by
    simpa only [he] using hbound H hH
  exact surviving_boundary_confined Z hx hbC (r H) hB (rep H) w hv hw'

end Heisenberg.HullRouting
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularComponents
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents Heisenberg.LatticeHull
variable {d : ℕ}

lemma component_exit (Z : Set (Site d)) {x y : Site d} (s : Finset (Site d))
    (hx : x ∈ s) (hy : y ∈ Component Z x) (hyout : y ∉ s) :
    ∃ u ∈ s, ∃ v ∈ Component Z x, v ∉ s ∧ v ∈ Ball 8 u := by
  have hr := hy.2
  have h : y ∈ s ∨ ∃ u ∈ s, ∃ v ∈ Component Z x, v ∉ s ∧ v ∈ Ball 8 u := by
    clear hyout
    induction hr with
    | refl => exact Or.inl hx
    | @tail u v hxu huv ih =>
      rcases ih ⟨huv.2.1,hxu⟩ with hu | he
      · by_cases hv : v ∈ s
        · exact Or.inl hv
        · exact Or.inr ⟨u,hu,v,⟨huv.2.2,hxu.tail huv⟩,hv,huv.1⟩
      · exact Or.inr he
  exact h.resolve_left hyout

lemma component_witness (Z : Set (Site d)) (hZ : Z.Finite) {x : Site d} (hx : x ∈ Z)
    (n : ℕ) (hn : n+1 ≤ (component_finite Z hZ x).toFinset.card) :
    ∃ s : Finset (Site d), x ∈ s ∧ s.card = n+1 ∧
      (∀ z ∈ s, z ∈ Component Z x) ∧ ∀ z ∈ s, z ∈ Ball (8*(n : ℤ)) x := by
  induction n with
  | zero =>
    refine ⟨{x},by simp,by simp,?_,?_⟩
    · intro z hz; simpa only [Finset.mem_singleton.mp hz] using self_mem_component Z hx
    · intro z hz; rw [Finset.mem_singleton.mp hz]; exact ball_self (by omega) x
  | succ n ih =>
    obtain ⟨s,hxs,hcard,hsC,hsball⟩ := ih (by omega)
    have hns : ¬ (component_finite Z hZ x).toFinset ⊆ s := by
      intro hsub
      have hc := Finset.card_le_card hsub
      omega
    obtain ⟨y,hyC,hys⟩ := Finset.not_subset.mp hns
    obtain ⟨u,hus,v,hvC,hvs,hvu⟩ := component_exit Z s hxs
      ((component_finite Z hZ x).mem_toFinset.mp hyC) hys
    refine ⟨insert v s,Finset.mem_insert_of_mem hxs,by simp [hvs,hcard],?_,?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hvC
      · exact hsC z hz
    · intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · simpa only [Nat.cast_succ,mul_add,mul_one] using ball_triangle (hsball u hus) hvu
      · exact ball_mono (by push_cast; omega) x (hsball z hz)

theorem small_component_of_local_count (Z : Set (Site d)) (hZ : Z.Finite)
    {x : Site d} (hx : x ∈ Z) (N : ℕ) (hN : 1 ≤ N)
    (hcount : (hZ.toFinset.filter (fun z => z ∈ Ball (8*((N-1 : ℕ) : ℤ)) x)).card < N) :
    (component_finite Z hZ x).toFinset.card < N := by
  by_contra h
  have hlarge : (N-1)+1 ≤ (component_finite Z hZ x).toFinset.card := by omega
  obtain ⟨s,_,hcard,hsC,hsB⟩ := component_witness Z hZ hx (N-1) hlarge
  have hs : s ⊆ hZ.toFinset.filter (fun z => z ∈ Ball (8*((N-1 : ℕ) : ℤ)) x) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨hZ.mem_toFinset.mpr (hsC z hz).1,hsB z hz⟩
  have hc := Finset.card_le_card hs
  have hlt : s.card < N := lt_of_le_of_lt hc hcount
  omega

theorem component_radius (Z : Set (Site d)) (hZ : Z.Finite)
    {x : Site d} (hx : x ∈ Z) :
    Component Z x ⊆ Ball (8*(((component_finite Z hZ x).toFinset.card-1 : ℕ) : ℤ)) x := by
  let C := (component_finite Z hZ x).toFinset
  have hpos : 1 ≤ C.card := by
    apply Finset.one_le_card.mpr
    exact ⟨x,(component_finite Z hZ x).mem_toFinset.mpr (self_mem_component Z hx)⟩
  obtain ⟨s,_,hcard,hsC,hsB⟩ := component_witness Z hZ hx (C.card-1) (by change C.card-1+1 ≤ C.card; omega)
  have hs : s ⊆ C := fun z hz => (component_finite Z hZ x).mem_toFinset.mpr (hsC z hz)
  have he : s = C := Finset.eq_of_subset_of_card_le hs (by omega)
  intro z hz
  apply hsB z
  rw [he]
  exact (component_finite Z hZ x).mem_toFinset.mpr hz

end Heisenberg.LatticeRegular

namespace Heisenberg.LatticeRegular
open Heisenberg.Geometry Heisenberg.LatticeComponents
variable {d : ℕ}

theorem regular_component_envelope (hd : 1 ≤ d) (Z : Set (Site d)) (hZ : Z.Finite)
    (x y : Site d) (R M : ℕ) (hM : 8*(2*d) ≤ M) (ν : ℝ)
    (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hy : y ∈ Ball (R:ℤ) x)
    (hreg : Regular Z x R M ν) :
    ∀ z ∈ Z, ∀ w ∈ Component Z z,
      dist z w ≤ (16*(d:ℝ)+2)*(1+dist z y)^ν := by
  intro z hz w hw
  have hp : 1 ≤ (1+dist z y)^ν := Real.one_le_rpow (by linarith [dist_nonneg (x:=z) (y:=y)]) hν0
  by_cases hnear : z ∈ Ball (10*R : ℕ) x
  · have hz11 : z ∈ Ball (11*R : ℕ) x := ball_mono (by omega) x hnear
    have hcount : (hZ.toFinset.filter (fun w => w ∈ Ball (8*((2*d-1 : ℕ):ℤ)) z)).card < 2*d := by
      apply lt_of_le_of_lt (Finset.card_le_card ?_) (hreg.1 z hz11)
      intro a ha
      obtain ⟨haZ,haB⟩ := Finset.mem_filter.mp ha
      apply Finset.mem_filter.mpr
      refine ⟨(mem_ballFinset ..).mpr ?_,hZ.mem_toFinset.mp haZ⟩
      apply ball_mono _ z haB
      have hh : 8*(2*d-1) ≤ M := (Nat.mul_le_mul_left 8 (Nat.sub_le ..)).trans hM
      exact_mod_cast hh
    have hc := small_component_of_local_count Z hZ hz (2*d) (by omega) hcount
    have hb := component_radius Z hZ hz hw
    have hb' : w ∈ Ball (16*d : ℕ) z := by
      apply ball_mono _ z hb
      have : 8*((component_finite Z hZ z).toFinset.card-1) ≤ 16*d := by omega
      exact_mod_cast this
    have hdist := (dist_le_iff_mem_ball z w).mpr hb'
    have hdR : (0:ℝ) ≤ d := Nat.cast_nonneg _
    push_cast at hdist
    have := mul_le_mul_of_nonneg_left hp (show 0 ≤ 16*(d:ℝ)+2 by positivity)
    nlinarith
  · have hremote := hreg.2 z hz hnear w hw
    have hfar : (10*R:ℕ) < dist x z := lt_of_not_ge (mt (dist_le_iff_mem_ball x z).mp hnear)
    have hxy : dist x y ≤ (R:ℝ) := (dist_le_iff_mem_ball x y).mpr hy
    have hzx : dist z x ≤ dist z y + (R:ℝ) := by
      have h := dist_triangle z y x
      rw [dist_comm y x] at h
      linarith
    have hcmp : 1+dist z x ≤ 2*(1+dist z y) := by
      rw [dist_comm x z] at hfar
      push_cast at hfar
      linarith [Nat.cast_nonneg (α:=ℝ) R]
    have hpow : (1+dist z x)^ν ≤ 2*(1+dist z y)^ν := by
      calc
        _ ≤ (2*(1+dist z y))^ν := Real.rpow_le_rpow (by positivity) hcmp hν0
        _ = (2:ℝ)^ν*(1+dist z y)^ν := Real.mul_rpow (by norm_num) (by positivity)
        _ ≤ 2*(1+dist z y)^ν := mul_le_mul_of_nonneg_right
          (Real.rpow_le_self_of_one_le (by norm_num) hν1.le) (Real.rpow_nonneg (by positivity) _)
    exact hremote.trans (hpow.trans (mul_le_mul_of_nonneg_right (by nlinarith [Nat.cast_nonneg (α:=ℝ) d])
      (Real.rpow_nonneg (by positivity) _)))

end Heisenberg.LatticeRegular

open scoped Classical
open Filter Topology
namespace Heisenberg.RoutingDecay

lemma eventually_half {ν C : ℝ} (hν : ν < 1) :
    ∃ T ≥ 1, ∀ t ≥ T, C*t^ν ≤ t/2 := by
  have hlim : Tendsto (fun t : ℝ => C*t^(ν-1)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (sub_pos.mpr hν)).const_mul C
    simpa only [neg_sub,mul_zero] using h
  obtain ⟨T,hT⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds (by norm_num : (0:ℝ)<1/2)))
  refine ⟨max 1 T,le_max_left ..,?_⟩
  intro t ht
  have ht1 : 1 ≤ t := (le_max_left ..).trans ht
  have hsmall := hT t ((le_max_right ..).trans ht)
  have he : t^ν = t^(ν-1)*t := by
    calc
      t^ν = t^((ν-1)+1) := by congr 1; ring
      _ = t^(ν-1)*t := by rw [Real.rpow_add (by linarith : 0<t),Real.rpow_one]
  rw [he]
  nlinarith

theorem comparable_radii {ν C : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ K ≥ 1, ∀ h t : ℝ, 0 ≤ h → 0 ≤ t →
      |h-t| ≤ C*(1+t)^ν →
      (1+t ≤ K*(1+h)) ∧ (1+h ≤ K*(1+t)) ∧
      C*(1+t)^ν ≤ (C*K^ν)*(1+h)^ν := by
  obtain ⟨T,hT,htail⟩ := eventually_half (C:=C) hν1
  let K := max (max 2 T) (C+1)
  have hK2 : 2 ≤ K := (le_max_left 2 T).trans (le_max_left ..)
  have hKT : T ≤ K := (le_max_right 2 T).trans (le_max_left ..)
  have hKC : C+1 ≤ K := le_max_right ..
  refine ⟨K,by linarith,?_⟩
  intro h t hh ht he
  have hab := abs_le.mp he
  have hlow : 1+t ≤ K*(1+h) := by
    by_cases hlarge : T ≤ 1+t
    · have hhalf := htail (1+t) hlarge
      have hrel : 1+t ≤ 2*(1+h) := by linarith
      exact hrel.trans (mul_le_mul_of_nonneg_right hK2 (by linarith))
    · have hsmall : 1+t ≤ K := (le_of_lt (lt_of_not_ge hlarge)).trans hKT
      exact hsmall.trans ((le_mul_iff_one_le_right (by linarith : 0<K)).mpr (by linarith))
  have hp : (1+t)^ν ≤ 1+t := Real.rpow_le_self_of_one_le (by linarith) hν1.le
  have hupp : 1+h ≤ K*(1+t) := by
    have hc := mul_le_mul_of_nonneg_left hp hC
    have hk := mul_le_mul_of_nonneg_right hKC (by linarith : 0≤1+t)
    nlinarith
  refine ⟨hlow,hupp,?_⟩
  calc
    _ ≤ C*(K*(1+h))^ν := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (by linarith) hlow hν0) hC
    _ = _ := by rw [Real.mul_rpow (by linarith) (by linarith)]; ring

variable {V : Type*} [PseudoMetricSpace V]

theorem neighborhood_displacement {ν C : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 1 ≤ C) :
    ∃ D ≥ 1, ∀ y u q c z : V,
      dist u q ≤ 1 →
      dist q c + 1 ≤ C*(1+dist c y)^ν →
      dist z c ≤ C*(1+dist c y)^ν →
      dist u z ≤ D*(1+dist u y)^ν := by
  obtain ⟨K,hK,hcomp⟩ := comparable_radii hν0 hν1 (by linarith : 0 ≤ C)
  let D := 2*(C*K^ν)
  have hKp : 1 ≤ K^ν := Real.one_le_rpow hK hν0
  have hCK : 1 ≤ C*K^ν := one_le_mul_of_one_le_of_one_le hC hKp
  refine ⟨D,by dsimp [D]; linarith,?_⟩
  intro y u q c z huq hqc hzc
  have huc : dist u c ≤ C*(1+dist c y)^ν :=
    (dist_triangle u q c).trans (by linarith)
  have hab : |dist u y-dist c y| ≤ C*(1+dist c y)^ν :=
    (abs_dist_sub_le u c y).trans huc
  have hp := (hcomp (dist u y) (dist c y) dist_nonneg dist_nonneg hab).2.2
  calc
    dist u z ≤ dist u c + dist c z := dist_triangle ..
    _ ≤ 2*(C*(1+dist c y)^ν) := by rw [dist_comm c z]; linarith
    _ ≤ 2*((C*K^ν)*(1+dist u y)^ν) := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = D*(1+dist u y)^ν := by dsimp [D]; ring

theorem inverse_displacement {ν D : ℝ} (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hD : 0 ≤ D) :
    ∃ (K : ℝ), 1 ≤ K ∧ ∀ y u v : V,
      dist u v ≤ D*(1+dist u y)^ν →
      1+dist v y ≤ K*(1+dist u y) ∧
      dist u v ≤ (D*K^ν)*(1+dist v y)^ν := by
  obtain ⟨K,hK,hcomp⟩ := comparable_radii hν0 hν1 hD
  refine ⟨K,hK,?_⟩
  intro y u v huv
  have hab : |dist v y-dist u y| ≤ D*(1+dist u y)^ν := by
    exact (abs_dist_sub_le v u y).trans (by simpa only [dist_comm v u] using huv)
  have h := hcomp (dist v y) (dist u y) dist_nonneg dist_nonneg hab
  exact ⟨h.2.1,huv.trans h.2.2⟩

end Heisenberg.RoutingDecay

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoutedNetworks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents
variable {d : ℕ}

theorem radial_hull_bounds (hd : 2 ≤ d) (Z : Set (Site d)) (hZ : Z.Finite)
    (y : Site d) (ν C : ℝ) (hν : 0 ≤ ν) (hC : 0 ≤ C)
    (hcomp : ∀ z ∈ Z, ∀ w ∈ Component Z z, dist z w ≤ C*(1+dist z y)^ν) :
    ∃ (b : Site d) (c : Set (Site d) → Site d) (r : Set (Site d) → ℕ),
      b ∉ Thick 4 Z ∧
      ∀ H ∈ maxHulls Z hZ b,
        H ⊆ Ball (r H : ℤ) (c H) ∧
        (r H : ℝ)+1 ≤ (C+6)*(1+dist (c H) y)^ν := by
  let ρ (z : Site d) : ℕ := ⌈C*(1+dist z y)^ν⌉₊+4
  have hrad (z : Site d) : (ρ z : ℝ)+1 ≤ (C+6)*(1+dist z y)^ν := by
    have hp : 1 ≤ (1+dist z y)^ν := Real.one_le_rpow (by linarith [dist_nonneg (x:=z) (y:=y)]) hν
    have hceil := Nat.ceil_lt_add_one (show 0 ≤ C*(1+dist z y)^ν from mul_nonneg hC (Real.rpow_nonneg (by positivity) _))
    dsimp [ρ]
    push_cast
    nlinarith
  have hthick (z : Site d) (hz : z ∈ Z) : Thick 4 (Component Z z) ⊆ Ball (ρ z : ℤ) z := by
    rintro w ⟨a,ha,hwa⟩
    have haB : a ∈ Ball (⌈C*(1+dist z y)^ν⌉₊ : ℤ) z :=
      (dist_le_iff_mem_ball z a).mp ((hcomp z hz a ha).trans (Nat.le_ceil _))
    simpa only [ρ,Nat.cast_add,Nat.cast_ofNat] using ball_triangle haB hwa
  let U : Set (Site d) := ⋃ z ∈ Z, Ball (ρ z : ℤ) z
  have hU : U.Finite := hZ.biUnion (fun z _ => ball_finite (ρ z) z)
  obtain ⟨N,hN⟩ := finite_contained_box U hU
  let b : Site d := fun _ => (N:ℤ)+1
  have hbN : b ∉ Box (N:ℤ) := by
    intro h
    have h0 := h ⟨0,by omega⟩
    simp only [b,abs_of_nonneg (by positivity : (0:ℤ) ≤ (N:ℤ)+1)] at h0
    omega
  have hb (z : Site d) (hz : z ∈ Z) : b ∉ Ball (ρ z : ℤ) z := by
    intro h
    apply hbN (hN ?_)
    exact Set.mem_iUnion.mpr ⟨z,Set.mem_iUnion.mpr ⟨hz,h⟩⟩
  have hbZ : b ∉ Thick 4 Z := by
    rintro ⟨z,hz,hbz⟩
    apply hb z hz
    exact ball_mono (by dsimp [ρ]; omega) z hbz
  have hroot : ∀ H ∈ maxHulls Z hZ b, ∃ z ∈ Z, Hull (Thick 4 (Component Z z)) b = H := by
    intro H hH
    exact (mem_allHulls ..).mp ((mem_maxHulls ..).mp hH).prop
  let c (H : Set (Site d)) : Site d := if h : H ∈ maxHulls Z hZ b then (hroot H h).choose else 0
  have hc (H : Set (Site d)) (hH : H ∈ maxHulls Z hZ b) :
      c H ∈ Z ∧ Hull (Thick 4 (Component Z (c H))) b = H := by
    simpa only [c,dite_eq_left hH] using (hroot H hH).choose_spec
  refine ⟨b,c,fun H => ρ (c H),hbZ,?_⟩
  intro H hH
  refine ⟨?_,hrad (c H)⟩
  simpa only [(hc H hH).2] using hull_subset_ball hd _ _ _ (by positivity) (hthick _ (hc H hH).1) (hb _ (hc H hH).1)

lemma collapse_finite_fibers (F : Finset (Set (Site d))) (rep : Set (Site d) → Site d)
    (hfin : ∀ H ∈ F, H.Finite) (w : Site d) : (collapse F rep ⁻¹' {w}).Finite := by
  apply ((F.finite_toSet.biUnion hfin).union (Set.finite_singleton w)).subset
  intro z hz
  by_cases h : ∃ H ∈ F, z ∈ H
  · obtain ⟨H,hH,hzH⟩ := h
    exact Or.inl (Set.mem_iUnion.mpr ⟨H,Set.mem_iUnion.mpr ⟨hH,hzH⟩⟩)
  · exact Or.inr (by simpa only [Set.mem_preimage,Set.mem_singleton_iff,collapse_free rep h] using hz)

end Heisenberg.HullRouting

namespace Heisenberg.Geometry
lemma walk_support_mem {d : ℕ} {U : Set (Site d)} {u v : Site d}
    (p : (latticeGraph U).Walk u v) (hu : u ∈ U) : ∀ z ∈ p.support, z ∈ U := by
  induction p with
  | nil => simpa only [SimpleGraph.Walk.support_nil,List.mem_singleton] using (fun z hz => hz ▸ hu)
  | @cons u v w huv p ih =>
    intro z hz
    simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact hu
    · exact ih huv.2.2 z hz
end Heisenberg.Geometry

namespace Heisenberg.HullRouting
open Heisenberg.Geometry Heisenberg.LatticeCut Heisenberg.LatticeHull Heisenberg.LatticeComponents
variable {d : ℕ}

lemma collapse_mem_region (Z : Set (Site d)) (F : Finset (Set (Site d)))
    (rep c : Set (Site d) → Site d) (r : Set (Site d) → ℕ)
    (hrep : ∀ H ∈ F, rep H ∈ Boundary H)
    (hbound : ∀ H ∈ F, H ⊆ Ball (r H:ℤ) (c H))
    (hsurvive : ∀ u, collapse F rep u ∉ Z) (u v : Site d) :
    collapse F rep u ∈ RouteRegion Z F (fun H => Ball ((r H:ℤ)+1) (c H)) u v := by
  refine ⟨?_,hsurvive u⟩
  by_cases h : ∃ H ∈ F, u ∈ H
  · unfold collapse
    rw [dite_eq_left h]
    exact Or.inr (Or.inr ⟨h.choose,h.choose_spec.1,Or.inl h.choose_spec.2,
      boundary_subset_ball _ _ _ (hbound _ h.choose_spec.1) (hrep _ h.choose_spec.1)⟩)
  · exact Or.inl (collapse_free rep h)

theorem radial_routing (hd : 2 ≤ d) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ D ≥ 1, ∀ (Z : Set (Site d)) (_hZ : Z.Finite) (y : Site d),
      (∀ z ∈ Z, ∀ w ∈ Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ ψ : Site d → Site d,
        (∀ u, ψ u ∉ Z) ∧ (∀ w, (ψ ⁻¹' {w}).Finite) ∧
        ∀ u v, Step u v → ∃ p : (latticeGraph Zᶜ).Walk (ψ u) (ψ v),
          p.IsPath ∧ ∀ z ∈ p.support, dist u z ≤ D*(1+dist u y)^ν := by
  obtain ⟨D,hD,hdisp⟩ := RoutingDecay.neighborhood_displacement (V:=Site d) hν0 hν1 (show 1 ≤ C+6 by linarith)
  refine ⟨D,hD,?_⟩
  intro Z hZ y hcomp
  obtain ⟨b,c,r,hb,hbound⟩ := radial_hull_bounds hd Z hZ y ν C hν0 hC hcomp
  obtain ⟨rep,hrep,hsurvive,hpaths⟩ := finite_hull_routing Z hZ b hb
  let F := maxHulls Z hZ b
  let ψ := collapse F rep
  refine ⟨ψ,hsurvive,?_,?_⟩
  · apply collapse_finite_fibers
    intro H hH
    exact (ball_finite (r H) (c H)).subset (hbound H hH).1
  · intro u v huv
    let U := RouteRegion Z F (fun H => Ball ((r H:ℤ)+1) (c H)) u v
    obtain ⟨p,hp⟩ := hpaths c (fun H => r H) (fun H hH => (hbound H hH).1) u v huv
    have hG : latticeGraph U ≤ latticeGraph Zᶜ := by
      intro a b hab
      exact ⟨hab.1,hab.2.1.2,hab.2.2.2⟩
    refine ⟨p.mapLe hG,hp.mapLe hG,?_⟩
    intro z hz
    rw [SimpleGraph.Walk.support_mapLe_eq_support] at hz
    have hstart : ψ u ∈ U := collapse_mem_region Z F rep c r hrep
      (fun H hH => (hbound H hH).1) hsurvive u v
    have hzU := walk_support_mem p hstart z hz
    have hunit : 1 ≤ D*(1+dist u y)^ν := one_le_mul_of_one_le_of_one_le hD
      (Real.one_le_rpow (by linarith [dist_nonneg (x:=u) (y:=y)]) hν0)
    rcases hzU.1 with rfl | rfl | ⟨H,hH,hincident,hzH⟩
    · exact (by simp : dist z z ≤ 1).trans hunit
    · exact (step_dist_le_one huv).trans hunit
    · have hzc : dist z (c H) ≤ (C+6)*(1+dist (c H) y)^ν := by
        have h := (dist_le_iff_mem_ball (r:=r H+1) (c H) z).mpr (by simpa only [Nat.cast_add,Nat.cast_one] using hzH)
        rw [dist_comm (c H) z] at h
        push_cast at h
        exact h.trans (hbound H hH).2
      have hqc (q : Site d) (hq : q ∈ H) : dist q (c H)+1 ≤ (C+6)*(1+dist (c H) y)^ν := by
        have h := (dist_le_iff_mem_ball (c H) q).mpr ((hbound H hH).1 hq)
        rw [dist_comm (c H) q] at h
        linarith [(hbound H hH).2]
      rcases hincident with huH | hvH
      · exact hdisp y u u (c H) z (by simp) (hqc u huH) hzc
      · exact hdisp y u v (c H) z (step_dist_le_one huv) (hqc v hvH) hzc

end Heisenberg.HullRouting

open scoped Classical
namespace Heisenberg.RoutedFlow

namespace Network
variable {V E : Type*} (N : Network V E)

lemma pairing_eq_sum (F : E → ℝ) (g : V →₀ ℝ) (s : Finset E)
    (hs : ∀ e, N.gradient g e ≠ 0 → e ∈ s) :
    N.pairing F g = ∑ e ∈ s, F e * N.gradient g e := by
  unfold pairing
  apply sum_eq_of_zero_off
  · intro e he hne
    rw [show N.gradient g e = 0 from by_contra (fun h => hne (hs e h)),mul_zero]
  · intro e he hne
    rw [N.gradient_zero_of_not_mem g hne,mul_zero]

end Network

variable {V E W T : Type*}

namespace Routing
variable {S : Network V E} {N : Network W T} {ψ : V → W} (R : Routing S N ψ)

lemma mem_sources (s : Finset T) (e : E) : e ∈ R.sources s ↔ ∃ t ∈ s, R.current e t ≠ 0 := by
  simp [sources]

lemma push_eq_sum (F : E → ℝ) (s : Finset T) {t : T} (ht : t ∈ s) :
    R.push F t = ∑ e ∈ R.sources s, F e * R.current e t := by
  unfold push
  apply Finset.sum_subset
  · intro e he
    exact (R.mem_sources s e).mpr ⟨t,ht,(R.locallyFinite t).mem_toFinset.mp he⟩
  · intro e he hne
    rw [show R.current e t = 0 from by simpa using hne, mul_zero]

lemma pairing_push (F : E → ℝ) (g : W →₀ ℝ) :
    N.pairing (R.push F) g =
      ∑ e ∈ R.sources (N.edges g), F e * N.pairing (R.current e) g := by
  unfold Network.pairing
  calc
    _ = ∑ t ∈ N.edges g, ∑ e ∈ R.sources (N.edges g),
          F e * R.current e t * N.gradient g t := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [R.push_eq_sum F _ ht,Finset.sum_mul]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro t _
      ring

lemma source_gradient_zero (hψ : ∀ w, (ψ ⁻¹' {w}).Finite) (g : W →₀ ℝ)
    {e : E} (he : e ∉ R.sources (N.edges g)) : S.gradient (pullback ψ hψ g) e = 0 := by
  have hzero : N.pairing (R.current e) g = 0 := by
    apply Finset.sum_eq_zero
    intro t ht
    have hct : R.current e t = 0 := by
      by_contra h
      exact he ((R.mem_sources _ e).mpr ⟨t,ht,h⟩)
    rw [hct,zero_mul]
  rw [R.telescopes] at hzero
  exact hzero

theorem push_unit (hψ : ∀ w, (ψ ⁻¹' {w}).Finite) (F : E → ℝ) (y : V)
    (hF : S.UnitFlow F y) : N.UnitFlow (R.push F) (ψ y) := by
  intro g
  rw [R.pairing_push]
  have hsum := S.pairing_eq_sum F (pullback ψ hψ g) (R.sources (N.edges g))
    (fun e he => by_contra (fun h => he (R.source_gradient_zero hψ g h)))
  rw [show (∑ e ∈ R.sources (N.edges g), F e * N.pairing (R.current e) g) =
      S.pairing F (pullback ψ hψ g) from by
        rw [hsum]
        apply Finset.sum_congr rfl
        intro e _
        rw [R.telescopes]
        rfl]
  exact hF _

end Routing
end Heisenberg.RoutedFlow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_NetworkEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical

namespace Heisenberg.RoutedFlow.Network
variable {V E : Type*} (N : Network V E)

lemma vertex_sum (g : V →₀ ℝ) (e : E) :
    (∑ v ∈ g.support, g v * N.boundary e v) = N.gradient g e := by
  simp only [boundary,mul_sub,Finset.sum_sub_distrib,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_eq]
  rw [show (if N.src e ∈ g.support then g (N.src e) else 0) = g (N.src e) by
    split_ifs with h; rfl; exact (Finsupp.notMem_support_iff.mp h).symm]
  rw [show (if N.dst e ∈ g.support then g (N.dst e) else 0) = g (N.dst e) by
    split_ifs with h; rfl; exact (Finsupp.notMem_support_iff.mp h).symm]
  rfl

lemma boundary_zero {e : E} {v : V} (he : e ∉ (N.incidentFinite v).toFinset) :
    N.boundary e v = 0 := by
  have h : ¬(N.src e = v ∨ N.dst e = v) := by simpa using he
  simp [boundary,not_or.mp h |>.1,not_or.mp h |>.2]

lemma divergence_eq_sum (F : E → ℝ) (g : V →₀ ℝ) {v : V} (hv : v ∈ g.support) :
    N.divergence F v = ∑ e ∈ N.edges g, F e * N.boundary e v := by
  apply Finset.sum_subset
  · intro e he
    rcases (N.incidentFinite v).mem_toFinset.mp he with h|h
    · exact (N.mem_edges g e).mpr (Or.inl (h ▸ hv))
    · exact (N.mem_edges g e).mpr (Or.inr (h ▸ hv))
  · intro e _ he
    rw [N.boundary_zero he,mul_zero]

theorem pairing_divergence (F : E → ℝ) (g : V →₀ ℝ) :
    N.pairing F g = ∑ v ∈ g.support, g v * N.divergence F v := by
  unfold pairing
  simp_rw [← N.vertex_sum g]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v hv
  rw [N.divergence_eq_sum F g hv,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem unit_of_divergence (F : E → ℝ) (y : V)
    (h : ∀ v, N.divergence F v = if v = y then 1 else 0) : N.UnitFlow F y := by
  intro g
  rw [N.pairing_divergence]
  simp_rw [h,mul_ite,mul_one,mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hy
  · rfl
  · exact (Finsupp.notMem_support_iff.mp hy).symm

end Heisenberg.RoutedFlow.Network

namespace Heisenberg.RoutedFlow.Routing
variable {V E W T : Type*} {S : Network V E} {N : Network W T} {ψ : V → W}

theorem abs_push_le (R : Routing S N ψ) (F : E → ℝ) (t : T) (A : ℝ) (hA : 0 ≤ A)
    (hF : ∀ e, R.current e t ≠ 0 → |F e| ≤ A)
    (hR : ∀ e, |R.current e t| ≤ 1) :
    |R.push F t| ≤ ((R.locallyFinite t).toFinset.card : ℝ) * A := by
  unfold push
  calc
    _ ≤ ∑ e ∈ (R.locallyFinite t).toFinset, |F e * R.current e t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ (R.locallyFinite t).toFinset, A := by
      apply Finset.sum_le_sum
      intro e he
      rw [abs_mul]
      exact (mul_le_mul (hF e ((R.locallyFinite t).mem_toFinset.mp he)) (hR e)
        (abs_nonneg _) hA).trans_eq (mul_one A)
    _ = _ := by simp

end Heisenberg.RoutedFlow.Routing

namespace Heisenberg.RoutedFlow
variable {V : Type*} (G : SimpleGraph V) (hG : ∀ v, (G.neighborSet v).Finite)

variable {G}

omit hG in
lemma pathCurrent_abs_le_one {u v : V} (p : G.Walk u v) (hp : p.IsTrail) (e : G.Dart) :
    |pathCurrent p e| ≤ 1 := by
  rw [pathCurrent_eq_count,abs_of_nonneg (by positivity)]
  have hd : p.darts.Nodup := List.Nodup.of_map SimpleGraph.Dart.edge hp.edges_nodup
  exact_mod_cast List.nodup_iff_count_le_one.mp hd e

lemma routingOfPaths_abs_le_one {W E : Type*} (S : Network W E) (ψ : W → V)
    (P : ∀ e, G.Walk (ψ (S.src e)) (ψ (S.dst e)))
    (hP : ∀ t, {e | t ∈ (P e).darts}.Finite) (hsimple : ∀ e, (P e).IsTrail)
    (e : E) (t : G.Dart) : |(routingOfPaths hG S ψ P hP).current e t| ≤ 1 :=
  pathCurrent_abs_le_one (P e) (hsimple e) t

end Heisenberg.RoutedFlow

open scoped Classical
open Module
namespace Heisenberg.LatticeSum

lemma embed_injective (d : ℕ) : Function.Injective (embed (d := d)) := by
  intro x y h
  ext j
  have hj := congrFun (congrArg Subtype.val h) j
  change (x j : ℝ) = (y j : ℝ) at hj
  exact_mod_cast hj

lemma embed_norm_le {d : ℕ} (x : Site d) : ‖embed x‖ ≤ (radius x : ℝ) := by
  change ‖fun j => (x j : ℝ)‖ ≤ (radius x : ℝ)
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hj : (x j).natAbs ≤ radius x := by
    exact Finset.le_sup (α := ℕ) (f := fun j => (x j).natAbs) (Finset.mem_univ j)
  simpa only [Real.norm_eq_abs, Nat.cast_natAbs, Int.cast_abs] using
    (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast hj)

lemma embed_ne_zero {d : ℕ} {x : Site d} (hx : x ≠ 0) : embed x ≠ 0 := by
  intro he
  apply hx
  apply embed_injective d
  convert he using 1
  apply Subtype.ext
  funext j
  simp [embed]

theorem summable_radius_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) :
    Summable (fun x : Site d => ((radius x : ℝ) + 1) ^ r) := by
  have hrank : Module.finrank ℤ (integerLattice d) = d := by
    rw [ZLattice.rank ℝ]
    simp
  have hs := ZLattice.summable_norm_rpow (integerLattice d) r (by simpa [hrank] using hr)
  have ht : Summable (fun x : Site d => ‖embed x‖ ^ r) :=
    hs.comp_injective (embed_injective d)
  apply Summable.of_norm_bounded_eventually ht
  apply Set.Finite.subset (Set.finite_singleton (0 : Site d))
  intro x hx
  by_contra hn
  have hpos : 0 < ‖embed x‖ := norm_pos_iff.mpr (embed_ne_zero hn)
  have hle : ‖((radius x : ℝ) + 1) ^ r‖ ≤ ‖embed x‖ ^ r := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos (by positivity) _)]
    exact Real.rpow_le_rpow_of_nonpos hpos (by linarith [embed_norm_le x]) (by linarith)
  exact hx hle

theorem summable_radius_sub_rpow (d : ℕ) (r : ℝ) (hr : r < -(d : ℝ)) (y : Site d) :
    Summable (fun x : Site d => ((radius (x - y) : ℝ) + 1) ^ r) := by
  exact (Equiv.subRight y).summable_iff.mpr (summable_radius_rpow d r hr)

end Heisenberg.LatticeSum

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_LatticeFlows
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module

open scoped Classical

namespace Heisenberg.Flow

lemma layerMass_pos (k N : ℕ) : 0 < layerMass k N := by
  apply inv_pos.mpr
  exact_mod_cast Nat.choose_pos (by omega : k ≤ N + k)

lemma layerMass_zero (k : ℕ) : layerMass k 0 = 1 := by simp [layerMass]

lemma layerMass_recurrence (k N : ℕ) :
    layerMass k N * (N + 1) / (N + k + 1) = layerMass k (N + 1) := by
  have hc : (0 : ℝ) < (N + k).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ N + k)
  have hc' : (0 : ℝ) < (N + 1 + k).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ N + 1 + k)
  have he := Nat.choose_mul_succ_eq (N + k) k
  rw [show N + k + 1 - k = N + 1 by omega,
    show N + k + 1 = N + 1 + k by omega] at he
  have he' : ((N + k).choose k : ℝ) * (N + k + 1) =
      ((N + 1 + k).choose k : ℝ) * (N + 1) := by
    exact_mod_cast (by simpa [Nat.add_right_comm] using he)
  dsimp [layerMass]
  field_simp
  nlinarith [he']

lemma flow_nonneg {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) :
    0 ≤ orthantFlow n j := by
  unfold orthantFlow
  exact div_nonneg (mul_nonneg (layerMass_pos _ _).le (by positivity)) (by positivity)

lemma coord_le_level {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) : n j ≤ level n :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)

lemma outgoing {k : ℕ} (n : Orthant k) :
    ∑ j, orthantFlow n j = layerMass k (level n) := by
  have hs : (∑ j : Fin (k + 1), ((n j : ℝ) + 1)) = (level n : ℝ) + k + 1 := by
    simp [Finset.sum_add_distrib, level, Nat.cast_sum, add_assoc]
  simp only [orthantFlow, ← Finset.sum_div, ← Finset.mul_sum]
  rw [hs]
  exact mul_div_cancel_right₀ _ (by positivity)

lemma predecessor_level {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) (hj : 0 < n j) :
    level (predecessor n j) + 1 = level n := by
  have hp : predecessor n j j + 1 = n j := by simp [predecessor]; omega
  have he : ∑ i ∈ Finset.univ.erase j, predecessor n j i =
      ∑ i ∈ Finset.univ.erase j, n i := by
    apply Finset.sum_congr rfl
    intro i hi
    simp [predecessor, (Finset.mem_erase.mp hi).1]
  have hsum := Finset.sum_erase_add (Finset.univ : Finset (Fin (k + 1)))
    (predecessor n j) (Finset.mem_univ j)
  have hsum' := Finset.sum_erase_add (Finset.univ : Finset (Fin (k + 1)))
    n (Finset.mem_univ j)
  dsimp [level]
  omega

lemma level_zero_iff {k : ℕ} (n : Orthant k) : level n = 0 ↔ n = 0 := by
  constructor
  · intro h
    funext j
    have := coord_le_level n j
    simp only [Pi.zero_apply]
    omega
  · rintro rfl; simp [level]

lemma incoming {k : ℕ} (n : Orthant k) (hn : n ≠ 0) :
    ∑ j, (if 0 < n j then orthantFlow (predecessor n j) j else 0) =
      layerMass k (level n) := by
  have hN : 0 < level n := Nat.pos_of_ne_zero (mt (level_zero_iff n).mp hn)
  obtain ⟨N, hlev⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  have heach (j : Fin (k + 1)) :
      (if 0 < n j then orthantFlow (predecessor n j) j else 0) =
        layerMass k N * (n j : ℝ) / (N + k + 1) := by
    split_ifs with hj
    · have hp := predecessor_level n j hj
      have hp' : level (predecessor n j) = N := by omega
      have hj' : ((n j - 1 : ℕ) : ℝ) + 1 = n j := by exact_mod_cast Nat.sub_add_cancel hj
      rw [orthantFlow, hp']
      simp only [predecessor, Function.update_self]
      rw [hj']
    · have hj' : n j = 0 := by omega
      simp [hj']
  simp_rw [heach]
  rw [← Finset.sum_div, ← Finset.mul_sum, ← Nat.cast_sum]
  change layerMass k N * (level n : ℝ) / _ = _
  rw [hlev]
  push_cast
  exact layerMass_recurrence k N

theorem orthant_divergence {k : ℕ} (n : Orthant k) :
    (∑ j, orthantFlow n j) -
      (∑ j, if 0 < n j then orthantFlow (predecessor n j) j else 0) =
        if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · subst n
    simp [outgoing, level, layerMass_zero]
  · rw [outgoing, incoming n hn, sub_self, ite_eq_right hn]

lemma flow_le_layerMass {k : ℕ} (n : Orthant k) (j : Fin (k + 1)) :
    orthantFlow n j ≤ layerMass k (level n) := by
  unfold orthantFlow
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < level n + k + 1)).mpr
  apply mul_le_mul_of_nonneg_left _ (layerMass_pos _ _).le
  have hc : (n j : ℝ) ≤ level n := by exact_mod_cast coord_le_level n j
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  linarith

lemma layerMass_decay (k N : ℕ) :
    layerMass k N ≤ (k.factorial : ℝ) / (N + 1) ^ k := by
  have hprod := Nat.pow_succ_le_ascFactorial (N + 1) k
  rw [Nat.ascFactorial_eq_factorial_mul_choose] at hprod
  have hprod' : (N + 1 : ℝ) ^ k ≤ (k.factorial : ℝ) * (N + k).choose k := by
    exact_mod_cast hprod
  have hc : (0 : ℝ) < (N + k).choose k := by
    exact_mod_cast Nat.choose_pos (by omega : k ≤ N + k)
  have hn : (0 : ℝ) < (N + 1) ^ k := by positivity
  rw [layerMass, inv_eq_one_div, div_le_div_iff₀ hc hn]
  simpa using hprod'

theorem orthant_flow_envelope {k : ℕ} (n : Orthant k) (j : Fin (k + 1))
    (h : ℕ) (hh : h ≤ level n) :
    |orthantFlow n j| ≤ (k.factorial : ℝ) / (h + 1) ^ k := by
  rw [abs_of_nonneg (flow_nonneg n j)]
  apply (flow_le_layerMass n j).trans
  apply (layerMass_decay k (level n)).trans
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  gcongr

lemma down_positive {k : ℕ} (x : ZSite k) (j : Fin (k + 1))
    (hx : PositiveOrthant x) : PositiveOrthant (down x j) ↔ 0 < x j := by
  constructor
  · intro hp
    have := hp j
    simp only [down, Function.update_self] at this
    omega
  · intro hj i
    by_cases hi : i = j
    · subst i; simp only [down, Function.update_self]; omega
    · simpa [down, hi] using hx i

lemma positive_of_down {k : ℕ} (x : ZSite k) (j : Fin (k + 1))
    (hx : PositiveOrthant (down x j)) : PositiveOrthant x := by
  intro i
  by_cases hi : i = j
  · subst i
    have := hx j
    simp only [down, Function.update_self] at this
    omega
  · have := hx i
    simpa [down, hi] using this

lemma natPart_down {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) :
    natPart (down x j) = predecessor (natPart x) j := by
  funext i
  by_cases hi : i = j
  · subst i
    simp only [natPart, down, predecessor, Function.update_self]
    omega
  · simp [natPart, down, predecessor, hi]

lemma natPart_zero_iff {k : ℕ} (x : ZSite k) (hx : PositiveOrthant x) :
    natPart x = 0 ↔ x = 0 := by
  constructor
  · intro h
    funext j
    have hj := congrFun h j
    have := hx j
    simp only [natPart, Pi.zero_apply] at hj ⊢
    omega
  · rintro rfl; funext j; rfl

lemma lattice_incoming_formula {k : ℕ} (x : ZSite k) (hx : PositiveOrthant x)
    (j : Fin (k + 1)) :
    latticeFlow (down x j) j =
      if 0 < natPart x j then orthantFlow (predecessor (natPart x) j) j else 0 := by
  have hc : 0 < natPart x j ↔ 0 < x j := by simp [natPart]
  by_cases hj : 0 < x j
  · rw [latticeFlow, ite_eq_left ((down_positive x j hx).mpr hj),
      natPart_down, ite_eq_left (hc.mpr hj)]
  · rw [latticeFlow, ite_eq_right (mt (down_positive x j hx).mp hj),
      ite_eq_right (mt hc.mp hj)]

theorem lattice_divergence {k : ℕ} (x : ZSite k) :
    (∑ j, latticeFlow x j) - (∑ j, latticeFlow (down x j) j) =
      if x = 0 then 1 else 0 := by
  by_cases hx : PositiveOrthant x
  · simp only [latticeFlow, ite_eq_left hx]
    change (∑ j, orthantFlow (natPart x) j) -
      (∑ j, latticeFlow (down x j) j) = _
    simp_rw [lattice_incoming_formula x hx]
    simp only [orthant_divergence, natPart_zero_iff x hx]
  · have hn : x ≠ 0 := by rintro rfl; exact hx (by intro j; simp)
    have hp (j : Fin (k + 1)) : ¬PositiveOrthant (down x j) :=
      mt (positive_of_down x j) hx
    simp only [latticeFlow, ite_eq_right hx, ite_eq_right (hp _), Finset.sum_const_zero,
      sub_zero, ite_eq_right hn]

lemma radius_le_level {k : ℕ} (x : ZSite k) (hx : PositiveOrthant x) :
    radius x ≤ level (natPart x) := by
  apply Finset.sup_le
  intro j _
  have he : (x j).natAbs = (x j).toNat := by
    have ha := Int.natAbs_of_nonneg (hx j)
    have hb := Int.toNat_of_nonneg (hx j)
    omega
  rw [he]
  exact coord_le_level (natPart x) j

theorem lattice_flow_envelope {k : ℕ} (x : ZSite k) (j : Fin (k + 1)) :
    |latticeFlow x j| ≤ (k.factorial : ℝ) / (radius x + 1) ^ k := by
  by_cases hx : PositiveOrthant x
  · rw [latticeFlow, ite_eq_left hx]
    exact orthant_flow_envelope (natPart x) j _ (radius_le_level x hx)
  · rw [latticeFlow, ite_eq_right hx, abs_zero]
    positivity

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FlowRouting
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical

namespace Heisenberg.Flow

open RoutedFlow
variable {k : ℕ}

lemma next_ne (x : ZSite k) (j : Fin (k+1)) : next x j ≠ x := by
  intro h
  have hj := congrFun h j
  simp [next] at hj

lemma down_ne (x : ZSite k) (j : Fin (k+1)) : down x j ≠ x := by
  intro h
  have hj := congrFun h j
  simp [down] at hj

lemma incident_set (v : ZSite k) :
    ((latticeNetwork k).incidentFinite v).toFinset =
      (Finset.univ.image (fun j => (v,j))) ∪ (Finset.univ.image (fun j => (down v j,j))) := by
  ext ⟨x,j⟩
  simp only [Set.Finite.mem_toFinset,Set.mem_ofPred_eq,latticeNetwork,Finset.mem_union,
    Finset.mem_image,Finset.mem_univ,true_and,Prod.mk.injEq]
  constructor
  · rintro (h|h)
    · exact Or.inl ⟨j,h.symm,rfl⟩
    · exact Or.inr ⟨j,by rw [← h,down_next],rfl⟩
  · rintro (⟨i,h,rfl⟩|⟨i,h,rfl⟩)
    · exact Or.inl h.symm
    · exact Or.inr (by rw [← h,next_down])

lemma incident_disjoint (v : ZSite k) :
    Disjoint (Finset.univ.image (fun j : Fin (k+1) => (v,j)))
      (Finset.univ.image (fun j : Fin (k+1) => (down v j,j))) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp he
  obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hf
  have hji := congrArg Prod.snd hj
  change j = i at hji
  subst j
  exact down_ne v i (congrArg Prod.fst hj)

lemma latticeNetwork_divergence (F : ZSite k × Fin (k+1) → ℝ) (v : ZSite k) :
    (latticeNetwork k).divergence F v =
      (∑ j, F (v,j)) - ∑ j, F (down v j,j) := by
  rw [Network.divergence,incident_set,Finset.sum_union (incident_disjoint v)]
  rw [Finset.sum_image (by intro i _ j _ h; exact congrArg Prod.snd h),
    Finset.sum_image (by intro i _ j _ h; exact congrArg Prod.snd h)]
  simp [Network.boundary,latticeNetwork,next_ne,down_ne,sub_eq_add_neg]

end Heisenberg.Flow

namespace Heisenberg.Flow

section
open Heisenberg.Geometry Heisenberg.HullRouting Heisenberg.RoutedFlow
variable {k : ℕ}

lemma next_step (x : ZSite k) (j : Fin (k+1)) : Step x (next x j) := by
  refine ⟨j,Or.inl ?_,?_⟩
  · simp [next]
  · intro i hi
    simp [next,hi]

lemma down_sub (x y : ZSite k) (j : Fin (k+1)) : down x j-y = down (x-y) j := by
  ext i
  by_cases hi : i=j <;> simp [down,hi]
  omega

lemma translated_unit (y : ZSite k) :
    (latticeNetwork k).UnitFlow (fun e => latticeFlow (e.1-y) e.2) y := by
  apply Network.unit_of_divergence
  intro v
  rw [latticeNetwork_divergence]
  simp_rw [down_sub]
  have h := lattice_divergence (v-y)
  by_cases hv : v = y <;> simpa [sub_eq_zero,hv] using h

theorem routed_lattice (hk : 1 ≤ k) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ A ≥ 0, ∃ K ≥ 1, ∃ D ≥ 1, ∀ (Z : Set (ZSite k)) (_hZ : Z.Finite) (y : ZSite k),
      (∀ z ∈ Z, ∀ w ∈ LatticeComponents.Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ ψ : ZSite k → ZSite k,
        (∀ u, ψ u ∉ Z) ∧ (∀ u, dist u (ψ u) ≤ D*(1+dist u y)^ν) ∧ (∀ w, (ψ ⁻¹' {w}).Finite) ∧
        ∃ R : Routing (latticeNetwork k) (graphNetwork (latticeGraph Zᶜ)
          (lattice_neighbor_finite Zᶜ)) ψ,
          (∀ e t, |R.current e t| ≤ 1) ∧
          (∀ t, ((R.locallyFinite t).toFinset.card : ℝ) ≤
            (k+1:ℝ)*(2*⌈A*(1+dist t.fst y)^ν⌉₊+1)^ (k+1)) ∧
          (∀ e t, R.current e t ≠ 0 → 1+dist t.fst y ≤ K*(1+dist e.1 y)) ∧
          (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow
            (R.push (fun e => latticeFlow (e.1-y) e.2)) (ψ y) := by
  obtain ⟨D,hD,hroutes⟩ := radial_routing (d:=k+1) (by omega) ν C hν0 hν1 hC
  obtain ⟨K,hK,hreverse⟩ := RoutingDecay.inverse_displacement (V:=ZSite k) hν0 hν1 (by linarith : 0≤D)
  let A := D*K^ν
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A,hA,K,hK,D,hD,?_⟩
  intro Z hZ y hcomp
  obtain ⟨ψ,hψ,hfib,hP⟩ := hroutes Z hZ y hcomp
  choose P hsimple hdisp using fun e : ZSite k × Fin (k+1) => hP e.1 (next e.1 e.2) (next_step e.1 e.2)
  have hinverse (e : ZSite k × Fin (k+1)) (t : (latticeGraph Zᶜ).Dart) (ht : t ∈ (P e).darts) :
      1+dist t.fst y ≤ K*(1+dist e.1 y) ∧ dist e.1 t.fst ≤ A*(1+dist t.fst y)^ν :=
    hreverse y e.1 t.fst (hdisp e t.fst ((P e).dart_fst_mem_support_of_mem_darts ht))
  let B (t : (latticeGraph Zᶜ).Dart) :=
    (ballFinset (k+1) ⌈A*(1+dist t.fst y)^ν⌉₊ t.fst) ×ˢ (Finset.univ : Finset (Fin (k+1)))
  have hB (e : ZSite k × Fin (k+1)) (t : (latticeGraph Zᶜ).Dart) (ht : t ∈ (P e).darts) : e ∈ B t := by
    apply Finset.mem_product.mpr
    refine ⟨(mem_ballFinset ..).mpr ((dist_le_iff_mem_ball ..).mp ?_),Finset.mem_univ _⟩
    rw [dist_comm]
    exact (hinverse e t ht).2.trans (Nat.le_ceil _)
  have hfin (t : (latticeGraph Zᶜ).Dart) : {e | t ∈ (P e).darts}.Finite :=
    (B t).finite_toSet.subset (fun e he => hB e t he)
  let R := routingOfPaths (lattice_neighbor_finite Zᶜ) (latticeNetwork k) ψ P hfin
  refine ⟨ψ,hψ,?_,hfib,R,?_,?_,?_,?_⟩
  · intro u
    exact hdisp (u,0) (ψ u) (P (u,0)).start_mem_support
  · exact routingOfPaths_abs_le_one _ _ _ _ _ (fun e => (hsimple e).isTrail)
  · intro t
    have hsub : (R.locallyFinite t).toFinset ⊆ B t := by
      intro e he
      have h : R.current e t ≠ 0 := (R.locallyFinite t).mem_toFinset.mp he
      apply hB e t
      exact (pathCurrent_ne_zero_iff (P e) t).mp h
    have hc := Finset.card_le_card hsub
    have hbcard : (B t).card = (2*⌈A*(1+dist t.fst y)^ν⌉₊+1)^(k+1)*(k+1) := by
      dsimp [B]
      rw [Finset.card_product,ballFinset_card,Finset.card_univ,Fintype.card_fin]
    rw [hbcard] at hc
    rw [mul_comm] at hc
    exact_mod_cast hc
  · intro e t ht
    apply (hinverse e t ((pathCurrent_ne_zero_iff (P e) t).mp ht)).1
  · exact R.push_unit hfib _ _ (translated_unit y)

end

open Heisenberg.RoutedFlow Heisenberg.Geometry
variable {k : ℕ}

lemma radius_eq_norm (x : ZSite k) : (radius x : ℝ) = ‖x‖ := by
  apply le_antisymm
  · obtain ⟨j,hj,he⟩ := Finset.exists_mem_eq_sup Finset.univ (Finset.univ_nonempty) (fun j : Fin (k+1) => (x j).natAbs)
    change ((Finset.univ.sup (fun j => (x j).natAbs) : ℕ) : ℝ) ≤ ‖x‖
    rw [he]
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using norm_le_pi_norm x j
  · apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro j
    have h : (x j).natAbs ≤ radius x := Finset.le_sup (f:=fun j => (x j).natAbs) (Finset.mem_univ j)
    simpa only [Int.norm_eq_abs,Nat.cast_natAbs,Int.cast_abs] using (show ((x j).natAbs : ℝ) ≤ (radius x : ℝ) by exact_mod_cast h)

lemma lattice_flow_dist_bound (x y : ZSite k) (j : Fin (k+1)) :
    |latticeFlow (x-y) j| ≤ (k.factorial : ℝ) / (1+dist x y)^k := by
  simpa only [radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using lattice_flow_envelope (x-y) j

lemma congestion_bound (d : ℕ) {A ν r : ℝ} (hA : 0 ≤ A) (hν : 0 ≤ ν) (hr : 1 ≤ r) :
    (d:ℝ)*(2*⌈A*r^ν⌉₊+1)^d ≤ ((d:ℝ)*(2*A+3)^d)*r^((d:ℝ)*ν) := by
  have hp : 1 ≤ r^ν := Real.one_le_rpow hr hν
  have hn := Nat.ceil_lt_add_one (show 0 ≤ A*r^ν by positivity)
  have hbase : 2*(⌈A*r^ν⌉₊:ℝ)+1 ≤ (2*A+3)*r^ν := by nlinarith
  have hpow := pow_le_pow_left₀ (by positivity : 0 ≤ 2*(⌈A*r^ν⌉₊:ℝ)+1) hbase d
  have he : ((2*A+3)*r^ν)^d = (2*A+3)^d*r^((d:ℝ)*ν) := by
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast (r^ν),← Real.rpow_mul (by linarith : 0≤r),mul_comm ν]
  rw [he] at hpow
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg d)

lemma inverse_power_bound {K q r : ℝ} (_hk : 0 ≤ K) (hq : 0 < q) (hr : 0 < r)
    (h : r ≤ K*q) (n : ℕ) : 1/q^n ≤ K^n/r^n := by
  rw [div_le_div_iff₀ (pow_pos hq n) (pow_pos hr n),one_mul]
  simpa only [mul_pow] using pow_le_pow_left₀ hr.le h n

theorem routed_envelope (hk : 1 ≤ k) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1) (hC : 0 ≤ C) :
    ∃ B ≥ 0, ∃ D ≥ 1, ∀ (Z : Set (ZSite k)) (_hZ : Z.Finite) (y : ZSite k),
      (∀ z ∈ Z, ∀ w ∈ LatticeComponents.Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ a, a ∉ Z ∧ dist y a ≤ D ∧ ∃ J : (latticeGraph Zᶜ).Dart → ℝ,
        (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow J a ∧
        ∀ t, |J t| ≤ B*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by
  obtain ⟨A,hA,K,hK,D,hD,hroute⟩ := routed_lattice hk ν C hν0 hν1 hC
  let B := ((k+1:ℝ)*(2*A+3)^(k+1))*((k.factorial:ℝ)*K^k)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B,hB,D,hD,?_⟩
  intro Z hZ y hcomp
  obtain ⟨ψ,hψ,hψdist,_hfib,R,hcur,hcount,hcompare,hunit⟩ := hroute Z hZ y hcomp
  refine ⟨ψ y,hψ y,by simpa using hψdist y,R.push (fun e => latticeFlow (e.1-y) e.2),hunit,?_⟩
  intro t
  let r := 1+dist t.fst y
  have hr : 1 ≤ r := by dsimp [r]; linarith [dist_nonneg (x:=t.fst) (y:=y)]
  let F := (k.factorial:ℝ)*K^k/r^k
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hFe (e : ZSite k × Fin (k+1)) (he : R.current e t ≠ 0) : |latticeFlow (e.1-y) e.2| ≤ F := by
    have hq : 0 < 1+dist e.1 y := by linarith [dist_nonneg (x:=e.1) (y:=y)]
    have hi := inverse_power_bound (by linarith : 0≤K) hq (by linarith : 0<r) (hcompare e t he) k
    have hi' := mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg k.factorial)
    exact (lattice_flow_dist_bound e.1 y e.2).trans (by simpa only [F,div_eq_mul_inv,mul_assoc,one_mul] using hi')
  calc
    |R.push (fun e => latticeFlow (e.1-y) e.2) t| ≤ ((R.locallyFinite t).toFinset.card:ℝ)*F :=
      R.abs_push_le _ t F hF hFe (fun e => hcur e t)
    _ ≤ ((k+1:ℝ)*(2*⌈A*(1+dist t.fst y)^ν⌉₊+1)^(k+1))*F := mul_le_mul_of_nonneg_right (hcount t) hF
    _ ≤ (((k+1:ℝ)*(2*A+3)^(k+1))*r^((k+1:ℝ)*ν))*F :=
      mul_le_mul_of_nonneg_right (by simpa only [Nat.cast_add,Nat.cast_one,r] using congestion_bound (k+1) hA hν0 hr) hF
    _ = B*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by
      dsimp [B,F,r]
      rw [Real.rpow_sub (by positivity),Real.rpow_natCast]
      ring

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_FlowCongestion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical

namespace Heisenberg.Flow

section
open Heisenberg.Geometry Heisenberg.RoutedFlow
variable {k : ℕ}

lemma path_current_decay {Z : Set (ZSite k)} {y a : ZSite k}
    (p : (latticeGraph Zᶜ).Walk y a) (hp : p.IsTrail) {L q : ℝ}
    (hL : 0 ≤ L) (hq : 0 ≤ q) (hnear : ∀ z ∈ p.support, dist z y ≤ L)
    (t : (latticeGraph Zᶜ).Dart) :
    |pathCurrent p t| ≤ (1+L)^q*(1+dist t.fst y)^(-q) := by
  by_cases ht : pathCurrent p t = 0
  · rw [ht,abs_zero]; positivity
  have hz := hnear t.fst (p.dart_fst_mem_support_of_mem_darts ((pathCurrent_ne_zero_iff p t).mp ht))
  have hpos : 0 < 1+dist t.fst y := by positivity
  have hb := Real.rpow_le_rpow (by positivity : 0 ≤ 1+dist t.fst y) (by linarith : 1+dist t.fst y ≤ 1+L) hq
  have hpow : 0 < (1+dist t.fst y)^q := Real.rpow_pos_of_pos hpos _
  have hh : 1 ≤ (1+L)^q*(1+dist t.fst y)^(-q) := by
    rw [Real.rpow_neg hpos.le,mul_comm,← div_eq_inv_mul]
    exact (one_le_div hpow).mpr hb
  exact (pathCurrent_abs_le_one p hp t).trans hh

theorem connected_envelope (hk : 1 ≤ k) (ν C : ℝ) (hν0 : 0 ≤ ν) (hν1 : ν < 1)
    (hq : 0 ≤ (k:ℝ)-(k+1:ℝ)*ν) (hC : 0 ≤ C) :
    ∃ M : ℕ, ∃ B ≥ 0, ∀ (Z : Set (ZSite k)) (_hZ : Z.Finite) (y : ZSite k),
      y ∉ Z → ((ballFinset (k+1) M y).filter (· ∈ Z)).card < 2*(k+1) →
      (∀ z ∈ Z, ∀ w ∈ LatticeComponents.Component Z z, dist z w ≤ C*(1+dist z y)^ν) →
      ∃ J : (latticeGraph Zᶜ).Dart → ℝ,
        (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow J y ∧
        ∀ t, |J t| ≤ B*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by
  obtain ⟨B,hB,D,hD,hflow⟩ := routed_envelope hk ν C hν0 hν1 hC
  let K : ℕ := ⌈D⌉₊
  have hK : 1 ≤ K := by
    have hD' : (1:ℝ) ≤ (K:ℝ) := hD.trans (Nat.le_ceil _)
    exact_mod_cast hD'
  let M := K+2*(k+1)
  let q := (k:ℝ)-(k+1:ℝ)*ν
  let B' := B+(1+(M:ℝ))^q
  have hB' : 0 ≤ B' := add_nonneg hB (Real.rpow_nonneg (by positivity) _)
  refine ⟨M,B',hB',?_⟩
  intro Z hZ y hy hcount hcomp
  obtain ⟨a,ha,hay,J,hunit,hJ⟩ := hflow Z hZ y hcomp
  have haB : a ∈ Ball (K:ℤ) y := (dist_le_iff_mem_ball ..).mp (hay.trans (Nat.le_ceil _))
  obtain ⟨p,hp,_hlen⟩ := local_connectivity (by omega : 2 ≤ k+1) K hK y a Z haB hy ha hcount
  let hom : latticeGraph (Ball (M:ℤ) y \ Z) →g latticeGraph Zᶜ :=
    { toFun := id
      map_rel' := fun h => ⟨h.1,h.2.1.2,h.2.2.2⟩ }
  let P := p.map hom
  have hP : P.IsTrail := (hp.map (by exact Function.injective_id)).isTrail
  have hnear : ∀ z ∈ P.support, dist z y ≤ (M:ℝ) := by
    intro z hz
    have hzp : z ∈ p.support := by
      change z ∈ (p.map hom).support at hz
      rw [SimpleGraph.Walk.support_map,List.mem_map] at hz
      obtain ⟨z',hz',heq⟩ := hz
      change z' = z at heq
      exact heq ▸ hz'
    have hyU : y ∈ Ball ((K:ℤ)+2*(k+1:ℕ)) y \ Z := ⟨by intro j; simp; positivity,hy⟩
    have hzU := path_support_mem _ _ _ hyU p z hzp
    have hzB : z ∈ Ball (M:ℤ) y := by simpa only [M,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hzU.1
    simpa only [dist_comm] using (dist_le_iff_mem_ball y z).mpr hzB
  refine ⟨fun t => J t+pathCurrent P t,?_,?_⟩
  · intro g
    change (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).pairing (J + (pathCurrent P : (latticeGraph Zᶜ).Dart → ℝ)) g = g y
    rw [Network.pairing_add,hunit g,pathCurrent_pairing]
    change g a+(g y-g a)=g y
    ring
  · intro t
    have hpbound := path_current_decay P hP (by positivity : 0 ≤ (M:ℝ)) hq hnear t
    have hqeq : -q = (k+1:ℝ)*ν-k := by dsimp [q]; ring
    rw [hqeq] at hpbound
    calc
      _ ≤ |J t|+|pathCurrent P t| := abs_add_le _ _
      _ ≤ B*(1+dist t.fst y)^((k+1:ℝ)*ν-k)+(1+(M:ℝ))^q*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := add_le_add (hJ t) hpbound
      _ = B'*(1+dist t.fst y)^((k+1:ℝ)*ν-k) := by dsimp [B']; ring

end

open Heisenberg.Geometry Heisenberg.LatticeSum
variable {k : ℕ}

lemma edgeCode_injective (Z : Set (ZSite k)) : Function.Injective (edgeCode (Z:=Z)) := by
  intro e f h
  have hfst : e.fst = f.fst := congrArg Prod.snd h
  have hdiff : e.snd-e.fst = f.snd-f.fst := congrArg (fun p : ↥(ballFinset (k+1) 1 0) × ZSite k => (p.1 : ZSite k)) h
  have hsnd : e.snd = f.snd := by rw [hfst] at hdiff; exact sub_left_inj.mp hdiff
  exact SimpleGraph.Dart.ext e f (Prod.ext hfst hsnd)

end Heisenberg.Flow

open scoped Classical BigOperators
namespace Heisenberg.FlowOverlap

lemma weighted_half {a b H k q : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hH : 0 < H) (hq : 0 ≤ q) (hHa : H ≤ 2*a) :
    H^q*(a^(-k)*b^(-k)) ≤
      (2:ℝ)^q*(a^(-2*(k-q))+b^(-2*(k-q))) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  have hpow := Real.rpow_le_rpow hH.le hHa hq
  rw [Real.mul_rpow (by norm_num) ha0.le] at hpow
  have hbq : b^(-k) ≤ b^(-(k-q)) := Real.rpow_le_rpow_of_exponent_le hb (by linarith)
  have hea : a^q*a^(-k) = a^(-(k-q)) := by
    rw [←Real.rpow_add ha0]
    congr 1
    ring
  have hs (x : ℝ) (hx : 0 < x) : (x^(-(k-q)))^2 = x^(-2*(k-q)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hx.le]
    congr 1
    ring
  calc
    _ ≤ ((2:ℝ)^q*a^q)*(a^(-k)*b^(-k)) :=
      mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (2:ℝ)^q*(a^(-(k-q))*b^(-k)) := by rw [←hea]; ring
    _ ≤ (2:ℝ)^q*(a^(-(k-q))*b^(-(k-q))) := by gcongr
    _ ≤ (2:ℝ)^q*(a^(-2*(k-q))+b^(-2*(k-q))) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [←hs a ha0,←hs b hb0]
      nlinarith [sq_nonneg (a^(-(k-q))-b^(-(k-q))),sq_nonneg (a^(-(k-q))),sq_nonneg (b^(-(k-q)))]

lemma weighted_product {a b H k q : ℝ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hH : 0 < H) (hq : 0 ≤ q) (htri : H ≤ a+b) :
    a^(-k)*b^(-k) ≤ (2:ℝ)^q*H^(-q)*
      (a^(-2*(k-q))+b^(-2*(k-q))) := by
  have hw : H^q*(a^(-k)*b^(-k)) ≤
      (2:ℝ)^q*(a^(-2*(k-q))+b^(-2*(k-q))) := by
    by_cases haH : H ≤ 2*a
    · exact weighted_half ha hb hH hq haH
    · have hh := weighted_half (k:=k) hb ha hH hq (show H ≤ 2*b by linarith)
      simpa only [mul_comm (b^(-k)),add_comm (b^(-2*(k-q)))] using hh
  have hh := mul_le_mul_of_nonneg_left hw (Real.rpow_nonneg hH.le (-q))
  have hc : H^(-q)*H^q=1 := by rw [←Real.rpow_add hH]; simp
  calc
    _ = H^(-q)*(H^q*(a^(-k)*b^(-k))) := by rw [←mul_assoc,hc,one_mul]
    _ ≤ _ := by nlinarith [hh]

theorem overlap_sum {E V : Type*} [PseudoMetricSpace V]
    (site : E → V) (J K : E → ℝ) (y z : V) (C k q M : ℝ)
    (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hJ : ∀ e, |J e| ≤ C*(1+dist (site e) y)^(-k))
    (hK : ∀ e, |K e| ≤ C*(1+dist (site e) z)^(-k))
    (hy : Summable (fun e => (1+dist (site e) y)^(-2*(k-q))))
    (hz : Summable (fun e => (1+dist (site e) z)^(-2*(k-q))))
    (hyM : (∑' e, (1+dist (site e) y)^(-2*(k-q))) ≤ M)
    (hzM : (∑' e, (1+dist (site e) z)^(-2*(k-q))) ≤ M) :
    Summable (fun e => |J e*K e|) ∧
    (∑' e, |J e*K e|) ≤ (2*C^2*(2:ℝ)^q*M)*(1+dist y z)^(-q) := by
  let D := C^2*(2:ℝ)^q*(1+dist y z)^(-q)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hs : Summable (fun e => D*((1+dist (site e) y)^(-2*(k-q))+
      (1+dist (site e) z)^(-2*(k-q)))) := (hy.add hz).mul_left D
  have he : ∀ e, |J e*K e| ≤ D*((1+dist (site e) y)^(-2*(k-q))+
      (1+dist (site e) z)^(-2*(k-q))) := by
    intro e
    have ht := dist_triangle y (site e) z
    rw [dist_comm y (site e)] at ht
    have hp := weighted_product (k:=k) (q:=q)
      (show 1 ≤ 1+dist (site e) y by linarith [dist_nonneg (x:=site e) (y:=y)])
      (show 1 ≤ 1+dist (site e) z by linarith [dist_nonneg (x:=site e) (y:=z)])
      (show 0 < 1+dist y z by positivity) hq (by linarith)
    calc
      _ = |J e| * |K e| := abs_mul ..
      _ ≤ (C*(1+dist (site e) y)^(-k))*(C*(1+dist (site e) z)^(-k)) :=
        mul_le_mul (hJ e) (hK e) (abs_nonneg _) (by positivity)
      _ = C^2*((1+dist (site e) y)^(-k)*(1+dist (site e) z)^(-k)) := by ring
      _ ≤ C^2*((2:ℝ)^q*(1+dist y z)^(-q)*
          ((1+dist (site e) y)^(-2*(k-q))+(1+dist (site e) z)^(-2*(k-q)))) :=
        mul_le_mul_of_nonneg_left hp (sq_nonneg C)
      _ = _ := by dsimp [D]; ring
  have hsum := Summable.of_nonneg_of_le (fun _ => abs_nonneg _) he hs
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑' e, D*((1+dist (site e) y)^(-2*(k-q))+(1+dist (site e) z)^(-2*(k-q))) :=
      hsum.tsum_le_tsum he hs
    _ = D*((∑' e, (1+dist (site e) y)^(-2*(k-q)))+
        (∑' e, (1+dist (site e) z)^(-2*(k-q)))) := by rw [tsum_mul_left,hy.tsum_add hz]
    _ ≤ D*(M+M) := mul_le_mul_of_nonneg_left (add_le_add hyM hzM) hD
    _ = _ := by dsimp [D]; ring

end Heisenberg.FlowOverlap

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeSum
variable {k : ℕ}

lemma uniform_graph_sum (r : ℝ) (hr : r < -(k+1:ℝ)) :
    ∃ M ≥ 0, ∀ (Z : Set (ZSite k)) (y : ZSite k),
      Summable (fun e : (latticeGraph Zᶜ).Dart => (1+dist e.fst y)^r) ∧
      (∑' e : (latticeGraph Zᶜ).Dart, (1+dist e.fst y)^r) ≤ M := by
  let S := ∑' x : ZSite k, ((radius x:ℝ)+1)^r
  let M := (Fintype.card ↥(ballFinset (k+1) 1 0):ℝ)*S
  have hS : 0 ≤ S := tsum_nonneg (fun x => Real.rpow_nonneg (by positivity) _)
  refine ⟨M,mul_nonneg (Nat.cast_nonneg _) hS,?_⟩
  intro Z y
  have hs := summable_radius_sub_rpow (k+1) r (by push_cast; exact hr) y
  have htrans : (∑' x : ZSite k, ((radius (x-y):ℝ)+1)^r) = S :=
    (Equiv.subRight y).tsum_eq (fun x : ZSite k => ((radius x:ℝ)+1)^r)
  let F : ↥(ballFinset (k+1) 1 0) × ZSite k → ℝ :=
    fun e => ((radius (e.2-y):ℝ)+1)^r
  have hsF : Summable F := by
    apply (summable_prod_of_nonneg (fun _ => Real.rpow_nonneg (by positivity) _)).mpr
    exact ⟨fun _ => hs, .of_finite⟩
  have hcomp := hsF.comp_injective (edgeCode_injective Z)
  have hbound := tsum_comp_le_tsum_of_inj hsF
    (fun e => Real.rpow_nonneg (by positivity : 0 ≤ (radius (e.2-y):ℝ)+1) r) (edgeCode_injective Z)
  have htotal : (∑' e, F e) = M := by
    rw [hsF.tsum_prod,tsum_fintype]
    simp only [F,htrans,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    rfl
  refine ⟨?_,?_⟩
  · simpa only [Function.comp_def,F,edgeCode,radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hcomp
  · rw [htotal] at hbound
    simpa only [Function.comp_def,F,edgeCode,radius_eq_norm,dist_eq_norm,add_comm (1:ℝ)] using hbound

theorem graph_overlap_uniform (κ q C : ℝ) (hC : 0 ≤ C) (hq : 0 ≤ q)
    (hexp : (k+1:ℝ) < 2*(κ-q)) :
    ∃ B ≥ 0, ∀ (Z : Set (ZSite k)) (y z : ZSite k)
      (J K : (latticeGraph Zᶜ).Dart → ℝ),
      (∀ e, |J e| ≤ C*(1+dist e.fst y)^(-κ)) →
      (∀ e, |K e| ≤ C*(1+dist e.fst z)^(-κ)) →
      Summable (fun e => |J e*K e|) ∧
      (∑' e, |J e*K e|) ≤ B*(1+dist y z)^(-q) := by
  obtain ⟨M,hM,huniform⟩ := uniform_graph_sum (k:=k) (-2*(κ-q)) (by linarith)
  refine ⟨2*C^2*(2:ℝ)^q*M,by positivity,?_⟩
  intro Z y z J K hJ hK
  exact Heisenberg.FlowOverlap.overlap_sum (fun e : (latticeGraph Zᶜ).Dart => e.fst) J K y z C κ q M hC hq
    hJ hK (huniform Z y).1 (huniform Z z).1 (huniform Z y).2 (huniform Z z).2

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SparseEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators

open scoped Classical BigOperators
namespace Heisenberg.SparseSum

lemma dyadic_power (r : ℝ) (n : ℕ) : ((2:ℝ)^n)^r = ((2:ℝ)^r)^n := by
  rw [←Real.rpow_natCast,←Real.rpow_mul (by norm_num),mul_comm,
    Real.rpow_mul (by norm_num),Real.rpow_natCast]

theorem sparse_kernel_sum {I V : Type*} [Fintype I] [PseudoMetricSpace V]
    (x : I → V) (z : V) (α q L : ℝ) (hα : 0 ≤ α) (hαq : α < q) (hL : 0 ≤ L)
    (hgrowth : ∀ r : ℝ, 0 ≤ r →
      ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤ L*(1+r)^α) :
    (∑ i, (1+dist (x i) z)^(-q)) ≤
      (2:ℝ)^q * (L*(2:ℝ)^α) * (1-(2:ℝ)^(α-q))⁻¹ := by
  have hq : 0 < q := lt_of_le_of_lt hα hαq
  let a : ℝ := (2:ℝ)^(-q)
  have ha0 : 0 ≤ a := by dsimp [a]; positivity
  have ha1 : a < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs : Summable (fun n : ℕ => a^n) := (hasSum_geometric_of_lt_one ha0 ha1).summable
  let F : I → ℕ → ℝ := fun i n => if dist (x i) z ≤ (2:ℝ)^n then a^n else 0
  have hF : ∀ i n, 0 ≤ F i n := by intro i n; dsimp [F]; split_ifs <;> positivity
  have hsF : ∀ i, Summable (F i) := by
    intro i
    exact Summable.of_nonneg_of_le (hF i) (fun n => by dsimp [F]; split_ifs <;> simp [pow_nonneg ha0]) hs
  have hbound : ∀ i, (1+dist (x i) z)^(-q) ≤ (2:ℝ)^q*(∑' n, F i n) := by
    intro i
    obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near
      (show 1 ≤ 1+dist (x i) z by linarith [dist_nonneg (x:=x i) (y:=z)]) (by norm_num : (1:ℝ) < 2)
    have hd : dist (x i) z ≤ (2:ℝ)^(n+1) := by linarith
    have hp : (1+dist (x i) z)^(-q) ≤ ((2:ℝ)^n)^(-q) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) hn (by linarith)
    rw [dyadic_power] at hp
    have hprod : (2:ℝ)^q*a=1 := by dsimp [a]; rw [←Real.rpow_add (by norm_num)]; simp
    have he : ((2:ℝ)^(-q))^n = (2:ℝ)^q*a^(n+1) := by
      rw [pow_succ]
      calc
        _ = 1*a^n := by simp [a]
        _ = _ := by rw [←hprod]; ring
    rw [he] at hp
    apply hp.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := (hsF i).le_tsum (n+1) (fun j _ => hF i j)
    simpa only [F,ite_eq_left hd] using hh
  let b : ℝ := (2:ℝ)^(α-q)
  have hb0 : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hsb : Summable (fun n : ℕ => L*(2:ℝ)^α*b^n) :=
    (hasSum_geometric_of_lt_one hb0 hb1).summable.mul_left _
  have hc : ∀ n, (∑ i, F i n) ≤ L*(2:ℝ)^α*b^n := by
    intro n
    have hcount := hgrowth ((2:ℝ)^n) (by positivity)
    have ht : 1+(2:ℝ)^n ≤ 2*(2:ℝ)^n := by linarith [one_le_pow₀ (n:=n) (by norm_num : (1:ℝ) ≤ 2)]
    have hp := Real.rpow_le_rpow (by positivity) ht hα
    rw [Real.mul_rpow (by norm_num) (by positivity),dyadic_power] at hp
    calc
      _ = ((Finset.univ.filter (fun i => dist (x i) z ≤ (2:ℝ)^n)).card:ℝ)*a^n := by
        simp [F,←Finset.sum_filter]
      _ ≤ (L*(1+(2:ℝ)^n)^α)*a^n := mul_le_mul_of_nonneg_right hcount (pow_nonneg ha0 _)
      _ ≤ (L*((2:ℝ)^α*((2:ℝ)^α)^n))*a^n := by gcongr
      _ = _ := by
        have hab : (2:ℝ)^α*a=b := by dsimp [a,b]; rw [←Real.rpow_add (by norm_num)]; congr 1
        rw [show (L*((2:ℝ)^α*((2:ℝ)^α)^n))*a^n = L*(2:ℝ)^α*(((2:ℝ)^α)^n*a^n) by ring,
          ←mul_pow,hab]
  calc
    _ ≤ ∑ i, (2:ℝ)^q*(∑' n, F i n) := Finset.sum_le_sum (fun i _ => hbound i)
    _ = (2:ℝ)^q*(∑' n, ∑ i, F i n) := by
      rw [←Finset.mul_sum,←Summable.tsum_finsetSum (fun i _ => hsF i)]
    _ ≤ (2:ℝ)^q*(∑' n, L*(2:ℝ)^α*b^n) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact (summable_sum (fun i _ => hsF i)).tsum_le_tsum hc hsb
    _ = _ := by rw [tsum_mul_left,tsum_geometric_of_lt_one hb0 hb1]; dsimp [b]; ring

end Heisenberg.SparseSum

namespace Heisenberg.FlowAggregation

lemma kernel_displacement {V : Type*} [PseudoMetricSpace V]
    (x x' y y' : V) (R q : ℝ) (_hR : 0 ≤ R) (hq : 0 ≤ q)
    (hy : dist y x ≤ R) (hy' : dist y' x' ≤ R) :
    (1+dist y y')^(-q) ≤ if dist x x' ≤ 4*R then 1 else
      (2:ℝ)^q*(1+dist x x')^(-q) := by
  split_ifs with hn
  · exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [dist_nonneg (x:=y) (y:=y')]) (by linarith)
  · have ht : dist x x' ≤ 2*R+dist y y' := by
      have h := dist_triangle4 x y y' x'
      rw [dist_comm x y] at h
      linarith
    have hbase : 1+dist x x' ≤ 2*(1+dist y y') := by linarith [lt_of_not_ge hn]
    have hp := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < 1+dist x x') hbase (show -q ≤ 0 by linarith)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at hp
    have hc : (2:ℝ)^q*(2:ℝ)^(-q)=1 := by rw [←Real.rpow_add (by norm_num)]; simp
    have hh := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q)
    simpa only [←mul_assoc,hc,one_mul] using hh

lemma averaged_overlap {A B E : Type*} [Fintype A] [Fintype B]
    (μ : A → ℝ) (ν : B → ℝ) (J : A → E → ℝ) (K : B → E → ℝ) (C : ℝ)
    (hμ : ∀ a, 0 ≤ μ a) (hν : ∀ b, 0 ≤ ν b)
    (hm : ∑ a, μ a ≤ 1) (hn : ∑ b, ν b ≤ 1) (hC : 0 ≤ C)
    (hs : ∀ a b, Summable (fun e => |J a e*K b e|))
    (hb : ∀ a b, μ a ≠ 0 → ν b ≠ 0 → (∑' e, |J a e*K b e|) ≤ C) :
    Summable (fun e => |(∑ a, μ a*J a e)*(∑ b, ν b*K b e)|) ∧
    (∑' e, |(∑ a, μ a*J a e)*(∑ b, ν b*K b e)|) ≤ C := by
  let F : E → ℝ := fun e => ∑ a, ∑ b, (μ a*ν b)*|J a e*K b e|
  have hsF : Summable F := summable_sum (fun a _ => summable_sum (fun b _ => (hs a b).mul_left _))
  have hle : ∀ e, |(∑ a, μ a*J a e)*(∑ b, ν b*K b e)| ≤ F e := by
    intro e
    calc
      _ = |∑ a, ∑ b, (μ a*ν b)*(J a e*K b e)| := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ ≤ ∑ a, |∑ b, (μ a*ν b)*(J a e*K b e)| := Finset.abs_sum_le_sum_abs ..
      _ ≤ F e := by
        apply Finset.sum_le_sum
        intro a _
        simpa only [abs_mul,abs_of_nonneg (hμ a),abs_of_nonneg (hν _)] using
          (Finset.abs_sum_le_sum_abs (s:=Finset.univ) (f:=fun b => (μ a*ν b)*(J a e*K b e)))
  have hsres := Summable.of_nonneg_of_le (fun e => abs_nonneg _) hle hsF
  refine ⟨hsres,?_⟩
  calc
    _ ≤ ∑' e, F e := hsres.tsum_le_tsum hle hsF
    _ = ∑ a, ∑ b, (μ a*ν b)*(∑' e, |J a e*K b e|) := by
      rw [Summable.tsum_finsetSum (fun a _ => summable_sum (fun b _ => (hs a b).mul_left _))]
      apply Finset.sum_congr rfl
      intro a _
      rw [Summable.tsum_finsetSum (fun b _ => (hs a b).mul_left _)]
      simp only [tsum_mul_left]
    _ ≤ ∑ a, ∑ b, (μ a*ν b)*C := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      by_cases ha : μ a = 0
      · simp [ha]
      by_cases hb' : ν b = 0
      · simp [hb']
      exact mul_le_mul_of_nonneg_left (hb a b ha hb') (mul_nonneg (hμ a) (hν b))
    _ = (∑ a, μ a)*(∑ b, ν b)*C := by
      simp only [Finset.sum_mul,Finset.mul_sum]
      exact Finset.sum_comm
    _ ≤ C := by
      have hprod : (∑ a, μ a)*(∑ b, ν b) ≤ 1 := by
        exact (mul_le_mul hm hn (Finset.sum_nonneg (fun b _ => hν b)) (by norm_num)).trans_eq (by norm_num)
      simpa using mul_le_mul_of_nonneg_right hprod hC

lemma energy_le_row {I E : Type*} [Fintype I] (J : I → E → ℝ)
    (K : I → I → ℝ) (C : ℝ)
    (hs : ∀ i j, Summable (fun e => |J i e*J j e|))
    (hK : ∀ i j, (∑' e, |J i e*J j e|) ≤ K i j)
    (hrow : ∀ i, (∑ j, K i j) ≤ C) :
    Summable (fun e => (∑ i, J i e)^2) ∧
    (∑' e, (∑ i, J i e)^2) ≤ C*(Fintype.card I) := by
  let F : E → ℝ := fun e => ∑ i, ∑ j, |J i e*J j e|
  have hsF : Summable F := summable_sum (fun i _ => summable_sum (fun j _ => hs i j))
  have hb : ∀ e, (∑ i, J i e)^2 ≤ F e := by
    intro e
    calc
      _ = ∑ i, ∑ j, J i e*J j e := by rw [sq,Finset.sum_mul]; simp only [Finset.mul_sum]
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => le_abs_self _))
  have hsquare := Summable.of_nonneg_of_le (fun e => sq_nonneg _) hb hsF
  refine ⟨hsquare,?_⟩
  calc
    _ ≤ ∑' e, F e := hsquare.tsum_le_tsum hb hsF
    _ = ∑ i, ∑ j, ∑' e, |J i e*J j e| := by
      rw [Summable.tsum_finsetSum (fun i _ => summable_sum (fun j _ => hs i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact Summable.tsum_finsetSum (fun j _ => hs i j)
    _ ≤ ∑ i, ∑ j, K i j := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hK i j))
    _ ≤ ∑ _i : I, C := Finset.sum_le_sum (fun i _ => hrow i)
    _ = _ := by simp [mul_comm]

theorem injection_energy {I A E V : Type*} [Fintype I] [Fintype A] [PseudoMetricSpace V]
    (x : I → V) (y : I → A → V) (μ : I → A → ℝ) (J : I → A → E → ℝ)
    (α q L B : ℝ) (hα : 0 ≤ α) (hαq : α < q) (hL : 0 ≤ L) (hB : 0 ≤ B)
    (hgrowth : ∀ z r, 0 ≤ r →
      ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤ L*(1+r)^α)
    (hμ : ∀ i a, 0 ≤ μ i a) (hmass : ∀ i, ∑ a, μ i a ≤ 1)
    (hs : ∀ i a j b, Summable (fun e => |J i a e*J j b e|))
    (hoverlap : ∀ i a j b, (∑' e, |J i a e*J j b e|) ≤ B*(1+dist (y i a) (y j b))^(-q))
    (R : ℝ) (hR : 0 ≤ R) (hloc : ∀ i a, μ i a ≠ 0 → dist (y i a) (x i) ≤ R) :
    Summable (fun e => (∑ i, ∑ a, μ i a*J i a e)^2) ∧
    (∑' e, (∑ i, ∑ a, μ i a*J i a e)^2) ≤
      B*(L*(4:ℝ)^α + (2:ℝ)^q*((2:ℝ)^q*(L*(2:ℝ)^α)*(1-(2:ℝ)^(α-q))⁻¹)) *
        (1+R)^α*(Fintype.card I) := by
  let K : I → I → ℝ := fun i j => B*((if dist (x i) (x j) ≤ 4*R then 1 else 0) +
    (2:ℝ)^q*(1+dist (x i) (x j))^(-q))
  have hK : ∀ i j, 0 ≤ K i j := by intro i j; dsimp [K]; split_ifs <;> positivity
  have hover : ∀ i j, Summable (fun e => |(∑ a, μ i a*J i a e)*(∑ b, μ j b*J j b e)|) ∧
      (∑' e, |(∑ a, μ i a*J i a e)*(∑ b, μ j b*J j b e)|) ≤ K i j := by
    intro i j
    apply averaged_overlap (μ i) (μ j) (J i) (J j) (K i j) (hμ i) (hμ j) (hmass i) (hmass j) (hK i j) (hs i · j ·)
    intro a b ha hb
    apply (hoverlap i a j b).trans
    apply mul_le_mul_of_nonneg_left _ hB
    have hh := kernel_displacement (x i) (x j) (y i a) (y j b) R q hR (by linarith) (hloc i a ha) (hloc j b hb)
    have hp : 0 ≤ (2:ℝ)^q*(1+dist (x i) (x j))^(-q) := by positivity
    split_ifs at hh ⊢ <;> linarith
  apply energy_le_row (fun i e => ∑ a, μ i a*J i a e) K _ (fun i j => (hover i j).1) (fun i j => (hover i j).2)
  intro i
  have hcount := hgrowth (x i) (4*R) (by positivity)
  have hsum := Heisenberg.SparseSum.sparse_kernel_sum x (x i) α q L hα hαq hL (hgrowth (x i))
  have hrpow : (1+4*R)^α ≤ (4:ℝ)^α*(1+R)^α := by
    calc
      _ ≤ (4*(1+R))^α := Real.rpow_le_rpow (by positivity) (by linarith) hα
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  have hunit : 1 ≤ (1+R)^α := Real.one_le_rpow (by linarith) hα
  have hSS : 0 ≤ (2:ℝ)^q*(L*(2:ℝ)^α)*(1-(2:ℝ)^(α-q))⁻¹ := by
    have hh : (2:ℝ)^(α-q) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    positivity
  have he : (∑ j, K i j) = B*((Finset.univ.filter (fun j => dist (x j) (x i) ≤ 4*R)).card +
      (2:ℝ)^q*(∑ j, (1+dist (x j) (x i))^(-q))) := by
    simp only [K,←Finset.mul_sum,Finset.sum_add_distrib]
    simp [dist_comm]
  rw [he,mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hB
  nlinarith [mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q),
    mul_le_mul_of_nonneg_left hrpow hL,
    mul_nonneg (mul_nonneg (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q) hSS) (sub_nonneg.mpr hunit)]

end Heisenberg.FlowAggregation

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RegularKernels
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.LatticeComponents
open Heisenberg.RoutedFlow
variable {k : ℕ}

lemma regular_mono_M (Z : Set (ZSite k)) (x : ZSite k) (R M N : ℕ) (ν : ℝ)
    (hMN : M ≤ N) (h : Regular Z x R N ν) : Regular Z x R M ν := by
  refine ⟨fun z hz => lt_of_le_of_lt (Finset.card_le_card ?_) (h.1 z hz),h.2⟩
  intro w hw
  obtain ⟨hwB,hwZ⟩ := Finset.mem_filter.mp hw
  refine Finset.mem_filter.mpr ⟨?_,hwZ⟩
  apply (mem_ballFinset ..).mpr
  exact ball_mono (by exact_mod_cast hMN) z ((mem_ballFinset ..).mp hwB)

theorem regular_injection_energy (hk : 2 ≤ k) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∃ C ≥ 0, ∀ (I A : Type*) [Fintype I] [Fintype A]
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (x : I → ZSite k) (y : I → A → ZSite k)
      (μ : I → A → ℝ) (R : ℕ),
      (∀ i a,0 ≤ μ i a) → (∀ i,∑ a,μ i a ≤ 1) →
      (∀ z r,0 ≤ r → ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤
        L*(1+r)^((1:ℝ)/100)) →
      (∀ i a,μ i a ≠ 0 → y i a ∉ Z ∧ dist (y i a) (x i) ≤ R ∧
        Regular Z (x i) R M (1/(100*(k+1:ℝ)))) →
      ∃ J : I → A → (latticeGraph Zᶜ).Dart → ℝ,
        (∀ i a,μ i a ≠ 0 → (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow (J i a) (y i a)) ∧
        Summable (fun e => (∑ i,∑ a,μ i a*J i a e)^2) ∧
        (∑' e,(∑ i,∑ a,μ i a*J i a e)^2) ≤ C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I) := by
  let ν : ℝ := 1/(100*(k+1:ℝ))
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hdim : (0:ℝ) < k+1 := by positivity
  have hν : 0 ≤ ν := by dsimp [ν]; positivity
  have hν1 : ν < 1 := by dsimp [ν]; rw [div_lt_iff₀ (by positivity)]; nlinarith
  have hprod : (k+1:ℝ)*ν = 1/100 := by dsimp [ν]; field_simp
  let κ : ℝ := (k:ℝ)-(k+1:ℝ)*ν
  have hκ : 0 ≤ κ := by dsimp [κ]; rw [hprod]; linarith
  have hexp : (k+1:ℝ) < 2*(κ-1/4) := by dsimp [κ]; rw [hprod]; linarith
  obtain ⟨M₀,B,hB,hflow⟩ := connected_envelope (k:=k) (by omega) ν (16*(k+1:ℝ)+2) hν hν1 hκ (by positivity)
  obtain ⟨D,hD,hoverlap⟩ := graph_overlap_uniform (k:=k) κ (1/4) B hB (by norm_num) hexp
  let M := max M₀ (8*(2*(k+1)))
  let C := D*(L*(4:ℝ)^((1:ℝ)/100) + (2:ℝ)^((1:ℝ)/4)*
    ((2:ℝ)^((1:ℝ)/4)*(L*(2:ℝ)^((1:ℝ)/100))*(1-(2:ℝ)^((1:ℝ)/100-1/4))⁻¹))
  have hC : 0 ≤ C := by
    have hh : (2:ℝ)^((1:ℝ)/100-1/4)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
    dsimp [C]
    positivity
  refine ⟨M,C,hC,?_⟩
  intro I A _ _ Z hZ x y μ R hμ hmass hgrowth hgood
  have hchoose : ∀ i a,∃ J : (latticeGraph Zᶜ).Dart → ℝ,
      (μ i a ≠ 0 → (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).UnitFlow J (y i a)) ∧
      ∀ e,|J e| ≤ B*(1+dist e.fst (y i a))^(-κ) := by
    intro i a
    by_cases ha : μ i a=0
    · refine ⟨0,by simp [ha],fun e => ?_⟩
      simpa using mul_nonneg hB (Real.rpow_nonneg (by positivity : 0≤1+dist e.fst (y i a)) (-κ))
    · obtain ⟨hz,hnear,hreg⟩ := hgood i a ha
      have hy : y i a ∈ Ball (R:ℤ) (x i) := (dist_le_iff_mem_ball ..).mp (by rwa [dist_comm])
      have hy11 : y i a ∈ Ball (11*R:ℕ) (x i) := ball_mono (by omega) _ hy
      have hreg₀ := regular_mono_M Z (x i) R M₀ M ν (le_max_left ..) hreg
      have henv := regular_component_envelope (by omega : 1 ≤ k+1) Z hZ (x i) (y i a) R M
        (le_max_right ..) ν hν hν1 hy hreg
      obtain ⟨J,hunit,hdecay⟩ := hflow Z hZ (y i a) hz (hreg₀.1 _ hy11) (by simpa only [Nat.cast_add,Nat.cast_one] using henv)
      refine ⟨J,fun _ => hunit,?_⟩
      have he : (k+1:ℝ)*ν-k = -κ := by dsimp [κ]; ring
      simpa only [he] using hdecay
  choose J hunit hdecay using hchoose
  have hov := fun i a j b => hoverlap Z (y i a) (y j b) (J i a) (J j b) (hdecay i a) (hdecay j b)
  have hen := Heisenberg.FlowAggregation.injection_energy x y μ J (1/100) (1/4) L D
    (by norm_num) (by norm_num) hL hD hgrowth hμ hmass (fun i a j b => (hov i a j b).1)
    (fun i a j b => (hov i a j b).2) (R:ℝ) (Nat.cast_nonneg _)
    (fun i a ha => (hgood i a ha).2.1)
  exact ⟨J,hunit,hen.1,hen.2⟩

end Heisenberg.Flow

namespace Heisenberg.SlotMaximum
variable {X I : Type*}

lemma dominates (s : Finset I) (v : I → ℝ) {i : I} (hi : i ∈ s) :
    v i ≤ value s v := by
  rw [value,dite_eq_left ⟨i,hi⟩]
  exact Finset.le_max' _ _ (Finset.mem_image.mpr ⟨i,hi,rfl⟩)

theorem edge_energy (s t : Finset I) (hs : s.Nonempty) (ht : t.Nonempty)
    (v w : I → ℝ) :
    (value s v-value t w)^2 ≤ ∑ i ∈ s, ∑ j ∈ t,(v i-w j)^2 := by
  obtain ⟨i,hi,hei⟩ := attained hs v
  obtain ⟨j,hj,hej⟩ := attained ht w
  rw [hei,hej]
  exact (Finset.single_le_sum (fun b _ => sq_nonneg (v i-w b)) hj).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg (v a-w b))) hi)

end Heisenberg.SlotMaximum

namespace Heisenberg.RoutedFlow.Network
variable {X E I L : Type*} [Fintype I]
open Heisenberg.SlotMaximum

lemma pairing_square_bound (N : Network X E) (J : E → ℝ) (g : X →₀ ℝ)
    (hs : Summable (fun e => (J e)^2)) :
    (N.pairing J g)^2 ≤ (∑' e,(J e)^2)*(∑ e ∈ N.edges g,(N.gradient g e)^2) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (N.edges g) J (N.gradient g)
  have ht := Summable.sum_le_tsum (N.edges g) (fun e _ => sq_nonneg (J e)) hs
  exact hc.trans (mul_le_mul_of_nonneg_right ht (Finset.sum_nonneg (fun e _ => sq_nonneg _)))

lemma pairing_injections (N : Network X E) (μ : I → ℝ) (y : I → X)
    (J : I → E → ℝ) (hJ : ∀ i, μ i ≠ 0 → N.UnitFlow (J i) (y i)) (g : X →₀ ℝ) :
    N.pairing (fun e => ∑ i,μ i*J i e) g = ∑ i,μ i*g (y i) := by
  simp only [pairing,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [mul_assoc,←Finset.mul_sum]
  by_cases hi : μ i=0
  · simp [hi]
  · rw [show (∑ e ∈ N.edges g,J i e*N.gradient g e)=g (y i) from hJ i hi g]

theorem slot_injection_bound (N : Network X E) (s : X → Finset L)
    (v : X → L → ℝ) (F : Finset X)
    (hvF : ∀ x,x ∉ F → ∀ a ∈ s x,v x a=0)
    (hv : ∀ x a,0 ≤ v x a)
    (hs : ∀ e ∈ N.edges (test s v F hvF),
      (s (N.src e)).Nonempty ∧ (s (N.dst e)).Nonempty)
    (μ : I → ℝ) (hμ : ∀ i,0 ≤ μ i) (y : I → X) (a : I → L)
    (ha : ∀ i,μ i ≠ 0 → a i ∈ s (y i))
    (J : I → E → ℝ) (hJ : ∀ i,μ i ≠ 0 → N.UnitFlow (J i) (y i))
    (A : ℝ) (hA : 0 ≤ A)
    (hJs : Summable (fun e => (∑ i,μ i*J i e)^2))
    (hJE : (∑' e,(∑ i,μ i*J i e)^2) ≤ A) :
    (∑ i, μ i*v (y i) (a i))^2 ≤ A *
      ∑ e ∈ N.edges (test s v F hvF),
        ∑ b ∈ s (N.src e),∑ c ∈ s (N.dst e),(v (N.src e) b-v (N.dst e) c)^2 := by
  let g := test s v F hvF
  let K : E → ℝ := fun e => ∑ i,μ i*J i e
  have hi : (∑ i,μ i*v (y i) (a i)) ≤ N.pairing K g := by
    rw [pairing_injections N μ y J hJ]
    apply Finset.sum_le_sum
    intro i _
    by_cases h : μ i=0
    · simp [h]
    · exact mul_le_mul_of_nonneg_left (dominates _ _ (ha i h)) (hμ i)
  have hi0 : 0 ≤ ∑ i,μ i*v (y i) (a i) := Finset.sum_nonneg (fun i _ => mul_nonneg (hμ i) (hv _ _))
  have hc := pairing_square_bound N K g hJs
  have hgrad : (∑ e ∈ N.edges g,(N.gradient g e)^2) ≤
      ∑ e ∈ N.edges g,∑ b ∈ s (N.src e),∑ c ∈ s (N.dst e),
        (v (N.src e) b-v (N.dst e) c)^2 := by
    apply Finset.sum_le_sum
    intro e he
    exact edge_energy _ _ (hs e he).1 (hs e he).2 _ _
  calc
    _ ≤ (N.pairing K g)^2 := sq_le_sq₀ hi0 (hi0.trans hi) |>.mpr hi
    _ ≤ _ := hc.trans ((mul_le_mul_of_nonneg_right hJE
      (Finset.sum_nonneg (fun e _ => sq_nonneg _))).trans (mul_le_mul_of_nonneg_left hgrad hA))

end Heisenberg.RoutedFlow.Network

namespace Heisenberg.Flow

section
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow
open Heisenberg.SlotMaximum
variable {k : ℕ}

theorem regular_slot_test (hk : 2 ≤ k) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∃ C ≥ 0, ∀ (I A B : Type*) [Fintype I] [Fintype A]
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (x : I → ZSite k) (y : I → A → ZSite k)
      (μ : I → A → ℝ) (R : ℕ) (s : ZSite k → Finset B)
      (slot : I → A → B) (v : ZSite k → B → ℝ) (F : Finset (ZSite k))
      (hvF : ∀ z,z ∉ F → ∀ a ∈ s z,v z a=0),
      (∀ i a,0 ≤ μ i a) → (∀ i,∑ a,μ i a ≤ 1) →
      (∀ z r,0 ≤ r → ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card:ℝ) ≤
        L*(1+r)^((1:ℝ)/100)) →
      (∀ i a,μ i a ≠ 0 → y i a ∉ Z ∧ dist (y i a) (x i) ≤ R ∧
        Regular Z (x i) R M (1/(100*(k+1:ℝ)))) →
      (∀ z,z ∉ Z → (s z).Nonempty) →
      (∀ i a,μ i a ≠ 0 → slot i a ∈ s (y i a)) →
      (∀ z a,0 ≤ v z a) →
      (∑ i,∑ a,μ i a*v (y i a) (slot i a))^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I)) *
        ∑ e ∈ (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).edges
          (test s v F hvF),∑ a ∈ s e.fst,∑ b ∈ s e.snd,(v e.fst a-v e.snd b)^2 := by
  obtain ⟨M,C,hC,hflow⟩ := regular_injection_energy hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I A B _ _ Z hZ x y μ R s slot v F hvF hμ hmass hgrowth hgood havail hslot hv
  obtain ⟨J,hJ,hs,hbound⟩ := hflow I A Z hZ x y μ R hμ hmass hgrowth hgood
  let N := graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)
  have ha : ∀ e ∈ N.edges (test s v F hvF),(s (N.src e)).Nonempty ∧ (s (N.dst e)).Nonempty := by
    intro e _
    exact ⟨havail e.fst e.adj.2.1,havail e.snd e.adj.2.2⟩
  have h := Network.slot_injection_bound N s v F hvF hv ha
    (I:=I×A) (fun ia => μ ia.1 ia.2) (fun ia => hμ ia.1 ia.2)
    (fun ia => y ia.1 ia.2) (fun ia => slot ia.1 ia.2) (fun ia => hslot ia.1 ia.2)
    (fun ia => J ia.1 ia.2) (fun ia => hJ ia.1 ia.2)
    (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I)) (by positivity)
    (by simpa only [Fintype.sum_prod_type] using hs)
    (by simpa only [Fintype.sum_prod_type] using hbound)
  simpa only [Fintype.sum_prod_type, N, graphNetwork] using h

end

open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SlotMaximum
variable {k : ℕ}

lemma goodMass_nonneg {I V : Type*} (K : V → I → ℝ) (hK : ∀ j i,0≤K j i)
    (x : I → ZSite k) (y : V → ZSite k) (Z : Set (ZSite k)) (R M : ℕ) (i : I) (j : V) :
    0≤goodMass K x y Z R M i j := by
  unfold goodMass
  split_ifs
  · exact hK j i
  · rfl

theorem kernel_pairing_split {I V : Type*} [Fintype I] [Fintype V]
    (K : V → I → ℝ) (hK : ∀ j i,0≤K j i) (hm : ∀ i,∑ j,K j i≤1)
    (x : I → ZSite k) (y : V → ZSite k) (Z : Set (ZSite k)) (R M : ℕ)
    (v : V → ℝ) (hv : ∀ j,0≤v j ∧ v j≤1) :
    (∑ i,∑ j,K j i*v j) ≤
      (∑ i,if ¬Regular Z (x i) R M (1/(100*(k+1:ℝ))) then (1:ℝ) else 0)+
      (∑ i,∑ j,if (R:ℝ)<dist (y j) (x i) then K j i else 0)+
      (∑ i,∑ j,goodMass K x y Z R M i j*v j) := by
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  by_cases hr : Regular Z (x i) R M (1/(100*(k+1:ℝ)))
  · simp only [hr,not_true_eq_false,ite_false,zero_add,goodMass,true_and,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    by_cases hd : dist (y j) (x i)≤R
    · simp [hd,not_lt_of_ge hd]
    · have hh := mul_le_of_le_one_right (hK j i) (hv j).2
      simpa [hd,lt_of_not_ge hd] using hh
  · simp only [hr,not_false_eq_true,ite_true,goodMass,false_and,ite_false,zero_mul,Finset.sum_const_zero,add_zero]
    have hh := (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => mul_le_of_le_one_right (hK j i) (hv j).2)).trans (hm i)
    have hz : 0≤∑ j,if (R:ℝ)<dist (y j) (x i) then K j i else 0 := by
      apply Finset.sum_nonneg
      intro j _
      split_ifs
      · exact hK j i
      · rfl
    linarith

theorem regular_kernel_test (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (I V B : Type*) [Fintype I] [Fintype V]
      (K : V → I → ℝ) (x : I → ZSite k) (y : V → ZSite k)
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (R : ℕ) (s : ZSite k → Finset B)
      (slot : V → B) (v : ZSite k → B → ℝ) (F : Finset (ZSite k))
      (hvF : ∀ z,z∉F → ∀ a∈s z,v z a=0),
      (∀ j i,0≤K j i) → (∀ i,∑ j,K j i≤1) →
      (∀ z r,0≤r → ((Finset.univ.filter (fun i => dist (x i) z≤r)).card:ℝ) ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ j i,K j i≠0 → y j∉Z ∧ slot j∈s (y j)) →
      (∀ z,z∉Z → (s z).Nonempty) → (∀ z a,0≤v z a) →
      (∑ i,∑ j,goodMass K x y Z R M i j*v (y j) (slot j))^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I))*
        ∑ e ∈ (graphNetwork (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ)).edges (test s v F hvF),
          ∑ a∈s e.fst,∑ b∈s e.snd,(v e.fst a-v e.snd b)^2 := by
  obtain ⟨M,C,hC,hh⟩ := regular_slot_test hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I V B _ _ K x y Z hZ R s slot v F hvF hK hm hg hslot hav hv
  apply hh I V B Z hZ x (fun _ => y) (goodMass K x y Z R M) R s (fun _ => slot) v F hvF
  · exact goodMass_nonneg K hK x y Z R M
  · intro i
    apply le_trans (Finset.sum_le_sum (fun j _ => ?_)) (hm i)
    unfold goodMass
    split_ifs
    · rfl
    · exact hK j i
  · exact hg
  · intro i j hij
    unfold goodMass at hij
    split_ifs at hij with hh
    · exact ⟨(hslot j i hij).1,hh.2,hh.1⟩
    · contradiction
  · exact hav
  · intro i j hij
    unfold goodMass at hij
    split_ifs at hij
    · exact (hslot j i hij).2
    · contradiction
  · exact hv

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoutedDissipation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SlotMaximum
variable {X B : Type*}

lemma test_support_subset (s : X → Finset B) (v : X → B → ℝ) (F : Finset X)
    (hvF : ∀ x,x∉F → ∀ a∈s x,v x a=0) : (test s v F hvF).support⊆F := by
  intro x hx
  by_contra hn
  have hz := zero_of_zero (s x) (v x) (hvF x hn)
  exact (Finsupp.mem_support_iff.mp hx) hz

theorem finite_frame_energy (G : SimpleGraph X) (hG : ∀ x,(G.neighborSet x).Finite)
    (R : X → X → Prop) (hR : ∀ x y,G.Adj x y → R x y)
    (Λ F : Finset X) (hF : F⊆Λ)
    (hframe : ∀ x∈F,∀ y,G.Adj x y → y∈Λ)
    (s : X → Finset B) (v : X → B → ℝ)
    (hvF : ∀ x,x∉F → ∀ a∈s x,v x a=0) :
    (∑ e∈(graphNetwork G hG).edges (test s v F hvF),
      ∑ a∈s e.fst,∑ b∈s e.snd,(v e.fst a-v e.snd b)^2) ≤ frameEnergy R Λ s v := by
  let E := (graphNetwork G hG).edges (test s v F hvF)
  let f : X×X → ℝ := fun p => if R p.1 p.2 then
    ∑ a∈s p.1,∑ b∈s p.2,(v p.1 a-v p.2 b)^2 else 0
  have he (e : G.Dart) (h : e∈E) : e.fst∈Λ ∧ e.snd∈Λ := by
    have hh := (Network.mem_edges (graphNetwork G hG) (test s v F hvF) e).mp h
    rcases hh with hh|hh
    · have hhF := test_support_subset s v F hvF hh
      exact ⟨hF hhF,hframe e.fst hhF e.snd e.adj⟩
    · have hhF := test_support_subset s v F hvF hh
      exact ⟨hframe e.snd hhF e.fst e.adj.symm,hF hhF⟩
  have hnon (p : X×X) : 0≤f p := by
    dsimp [f]
    split_ifs
    · exact Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => sq_nonneg _))
    · rfl
  have hmap : E.image (fun e => e.toProd)⊆Λ×ˢΛ := by
    intro p hp
    obtain ⟨e,heE,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr (he e heE)
  calc
    _ = ∑ e∈E,f e.toProd := Finset.sum_congr rfl (fun e _ => by simp only [f,ite_eq_left (hR _ _ e.adj)])
    _ = ∑ p∈E.image (fun e => e.toProd),f p := by
      symm
      apply Finset.sum_image
      intro e _ d _ h
      exact SimpleGraph.Dart.ext e d h
    _ ≤ ∑ p∈Λ×ˢΛ,f p := Finset.sum_le_sum_of_subset_of_nonneg hmap (fun p _ _ => hnon p)
    _ = _ := by rw [Finset.sum_product]; rfl

variable {k : ℕ}

theorem regular_frame_test (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (I V B : Type*) [Fintype I] [Fintype V]
      (K : V → I → ℝ) (x : I → ZSite k) (y : V → ZSite k)
      (Z : Set (ZSite k)) (_hZ : Z.Finite) (R : ℕ) (s : ZSite k → Finset B)
      (slot : V → B) (v : ZSite k → B → ℝ) (Λ F : Finset (ZSite k))
      (_hvF : ∀ z,z∉F → ∀ a∈s z,v z a=0),
      F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
      (∀ j i,0≤K j i) → (∀ i,∑ j,K j i≤1) →
      (∀ z r,0≤r → ((Finset.univ.filter (fun i => dist (x i) z≤r)).card:ℝ) ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ j i,K j i≠0 → y j∉Z ∧ slot j∈s (y j)) →
      (∀ z,z∉Z → (s z).Nonempty) → (∀ z a,0≤v z a) →
      (∑ i,∑ j,goodMass K x y Z R M i j*v (y j) (slot j))^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I))*frameEnergy Step Λ s v := by
  obtain ⟨M,C,hC,htest⟩ := regular_kernel_test hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I V B _ _ K x y Z hZ R s slot v Λ F hvF hF hframe hK hm hg hs ha hv
  have hh := htest I V B K x y Z hZ R s slot v F hvF hK hm hg hs ha hv
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_frame_energy (latticeGraph Zᶜ) (lattice_neighbor_finite Zᶜ) Step
    (fun _ _ h => h.1) Λ F hF (fun z hz w h => hframe z hz w h.1) s v hvF

end Heisenberg.Flow

namespace Heisenberg.SpatialFrame

section
variable {X B : Type*} [Fintype B]

omit [Fintype B] in
lemma extend_apply (Λ : Finset X) (v : Slots (B:=B) Λ → ℝ) (x : Λ) (a : B) :
    extend Λ v x a=v (x,a) := by simp [extend]

lemma available_apply (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) (x : Λ) (a : B) :
    a∈available Λ H x ↔ (x,a)∈H := by simp [available]

lemma available_nonempty (Λ : Finset X) [Nonempty B] (H : Set (Slots (B:=B) Λ))
    (x : X) (hx : ¬∃ h : x∈Λ,∀ a : B,(⟨x,h⟩,a)∉H) :
    (available Λ H x).Nonempty := by
  by_cases h : x∈Λ
  · have hx : ∃ a : B,(⟨x,h⟩,a)∈H := by
      by_contra hn
      apply hx
      exact ⟨h,by simpa only [not_exists] using hn⟩
    obtain ⟨a,ha⟩ := hx
    exact ⟨a,by simpa [available,h] using ha⟩
  · simp [available,h]

omit [Fintype B] in
lemma extend_nonneg (Λ : Finset X) (v : Slots (B:=B) Λ → ℝ) (hv : ∀ j,0≤v j) :
    ∀ x a,0≤extend Λ v x a := by
  intro x a
  dsimp [extend]
  split_ifs
  · exact hv _
  · rfl

omit [Fintype B] in
lemma extend_supported (Λ F : Finset X) (v : Slots (B:=B) Λ → ℝ)
    (hv : ∀ j,j.1.val∉F → v j=0) : ∀ x,x∉F → ∀ a,extend Λ v x a=0 := by
  intro x hx a
  dsimp [extend]
  split_ifs
  · exact hv _ hx
  · rfl

lemma frame_eq_pairs (R : X → X → Prop) (Λ : Finset X)
    (H : Set (Slots (B:=B) Λ)) (v : Slots (B:=B) Λ → ℝ) :
    Heisenberg.Flow.frameEnergy R Λ (available Λ H) (extend Λ v) =
    ∑ e : Edges R Λ,if e.val.1∈H ∧ e.val.2∈H then (v e.val.1-v e.val.2)^2 else 0 := by
  unfold Heisenberg.Flow.frameEnergy
  simp_rw [←Finset.sum_coe_sort Λ]
  have he := Finset.sum_subtype
    (Finset.univ.filter (fun e : Slots (B:=B) Λ × Slots (B:=B) Λ => R e.1.1 e.2.1))
    (p:=fun e => R e.1.1 e.2.1) (F:=inferInstance) (by simp)
    (fun e => if e.1∈H ∧ e.2∈H then (v e.1-v e.2)^2 else 0)
  rw [←he]
  simp only [Finset.sum_filter,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hr : R x y
  · simp only [hr,ite_true,available,extend,dite_eq_left x.property,dite_eq_left y.property,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro a _
    by_cases hh : (x,a)∈H
    · simp only [hh,ite_true,true_and]
    · simp [hh]
  · simp [hr]

theorem frame_eq_sweep (R : X → X → Prop) (Λ : Finset X)
    (H : Set (Slots (B:=B) Λ)) (v : EuclideanSpace ℝ (Slots (B:=B) Λ))
    (a b : ℕ → Slots (B:=B) Λ) (n : ℕ)
    (e : Fin n ≃ Edges R Λ)
    (ha : ∀ i : Fin n,a i=(e i).val.1) (hb : ∀ i : Fin n,b i=(e i).val.2) :
    Heisenberg.Flow.frameEnergy R Λ (available Λ H) (extend Λ v.ofLp) =
      Heisenberg.Exposure.quietEnergy H a b n v := by
  rw [frame_eq_pairs]
  rw [←e.sum_comp]
  unfold Heisenberg.Exposure.quietEnergy
  rw [←Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [ha i,hb i]

end

variable {X B : Type*} [Fintype B]

omit [Fintype B] in
lemma blocked_finite (Λ : Finset X) (H : Set (Slots (B:=B) Λ)) :
    (blocked Λ H).Finite := Λ.finite_toSet.subset (fun _ h => h.choose)

omit [Fintype B] in
lemma hole_not_blocked (Λ : Finset X) (H : Set (Slots (B:=B) Λ))
    (j : Slots (B:=B) Λ) (hj : j∈H) : j.1.val∉blocked Λ H := by
  rintro ⟨h,hb⟩
  exact hb j.2 hj

lemma available_unblocked (Λ : Finset X) [Nonempty B] (H : Set (Slots (B:=B) Λ))
    (x : X) (hx : x∉blocked Λ H) : (available Λ H x).Nonempty := available_nonempty Λ H x hx
end Heisenberg.SpatialFrame

namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.RoutedFlow Heisenberg.SpatialFrame
variable {k : ℕ}

theorem routed_sweep_pair (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (I B : Type*) [Fintype I] [Fintype B] [Nonempty B]
      (Λ F : Finset (ZSite k)) (H : Set (Slots (B:=B) Λ))
      (x : I → ZSite k) (K : Slots (B:=B) Λ → I → ℝ)
      (v : EuclideanSpace ℝ (Slots (B:=B) Λ)) (R : ℕ)
      (a b : ℕ → Slots (B:=B) Λ) (n : ℕ) (e : Fin n ≃ Edges Step Λ),
      (∀ i : Fin n,a i=(e i).val.1) → (∀ i : Fin n,b i=(e i).val.2) →
      F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
      (∀ j,j.1.val∉F → v.ofLp j=0) →
      (∀ j i,0≤K j i) → (∀ i,∑ j,K j i≤1) →
      (∀ z r,0≤r → ((Finset.univ.filter (fun i => dist (x i) z≤r)).card:ℝ) ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ j i,K j i≠0 → j∈H) → (∀ j,0≤v.ofLp j) →
      (∑ i,∑ j,goodMass K x (fun j=>j.1.val) (blocked Λ H) R M i j*v.ofLp j)^2 ≤
        (C*(1+(R:ℝ))^((1:ℝ)/100)*(Fintype.card I))*
          Heisenberg.Exposure.quietEnergy H a b n v := by
  obtain ⟨M,C,hC,h⟩ := regular_frame_test hk L hL
  refine ⟨M,C,hC,?_⟩
  intro I B _ _ _ Λ F H x K v R a b n e ha hb hF hframe hvF hK hm hg hKH hv
  have hvext : ∀ z,z∉F → ∀ a∈available Λ H z,extend Λ v.ofLp z a=0 := by
    intro z hz a _
    exact extend_supported Λ F v.ofLp hvF z hz a
  have hs : ∀ j i,K j i≠0 → j.1.val∉blocked Λ H ∧ j.2∈available Λ H j.1 := by
    intro j i hji
    exact ⟨hole_not_blocked Λ H j (hKH j i hji),(available_apply Λ H j.1 j.2).mpr (hKH j i hji)⟩
  have hh := h I (Slots (B:=B) Λ) B K x (fun j=>j.1.val) (blocked Λ H)
    (blocked_finite Λ H) R (available Λ H) (fun j=>j.2) (extend Λ v.ofLp)
    Λ F hvext hF hframe hK hm hg hs (available_unblocked Λ H) (extend_nonneg Λ v.ofLp hv)
  simp only [extend_apply] at hh
  rw [frame_eq_sweep Step Λ H v a b n e ha hb] at hh
  exact hh

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_WeightedLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators

open scoped BigOperators Classical
namespace Heisenberg.FiniteLeakage

section

lemma weighted_young {A D b w p : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hb : 0 < b) (hp : p^2 ≤ A*D) :
    2*w*p ≤ b*D+A*w^2/b := by
  by_cases hz : A = 0
  · subst A
    have hp0 : p=0 := by nlinarith [sq_nonneg p]
    simp only [hp0,mul_zero,zero_mul,zero_div,add_zero]
    exact mul_nonneg hb.le hD
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm hz)
  have hh : 0 ≤ A*(b^2*D+A*w^2-2*b*w*p) := by
    have h1 := mul_nonneg (sq_nonneg b) (sub_nonneg.mpr hp)
    nlinarith [sq_nonneg (b*p-A*w)]
  have hn : 0 ≤ b^2*D+A*w^2-2*b*w*p := (mul_nonneg_iff_of_pos_left hAp).mp hh
  apply (mul_le_mul_iff_of_pos_right hb).mp
  field_simp
  nlinarith

lemma weighted_suffix {n : ℕ} (w G : Fin n → ℝ) :
    (∑ i, w i*(∑ j, if i ≤ j then G j else 0)) =
      ∑ j, (∑ i, if i ≤ j then w i else 0)*G j := by
  simp only [Finset.mul_sum,Finset.sum_mul,mul_ite,ite_mul,mul_zero,zero_mul]
  exact Finset.sum_comm

theorem weighted_leakage {n : ℕ} (w L err pair energy loss residual : Fin n → ℝ)
    (m final A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (hw : ∀ i, 0 ≤ w i) (hws : ∑ i, w i = 1)
    (hW : ∀ i, 0 < ∑ j, if j ≤ i then w j else 0)
    (henergy : ∀ i, 0 ≤ energy i)
    (hpair : ∀ i, (pair i)^2 ≤ A*energy i)
    (hloss : ∀ i, 2*δ*energy i ≤ loss i+residual i)
    (hlower : ∀ i, m-err i-2*pair i+(∑ j, if i ≤ j then loss j else 0) ≤ L i)
    (hfinal : ∀ i, L i ≤ final) :
    m-(∑ i, w i*err i)-
      (∑ i, A*(w i)^2/(2*δ*(∑ j, if j ≤ i then w j else 0)))-
      (∑ i, (∑ j, if j ≤ i then w j else 0)*residual i) ≤ final := by
  let W : Fin n → ℝ := fun i => ∑ j, if j ≤ i then w j else 0
  have hp : ∀ i, 2*w i*pair i ≤ W i*loss i+W i*residual i+
      A*(w i)^2/(2*δ*W i) := by
    intro i
    have hh := weighted_young (w := w i) hA (henergy i) (show 0 < 2*δ*W i from mul_pos (mul_pos (by norm_num) hδ) (hW i)) (hpair i)
    have he := mul_le_mul_of_nonneg_left (hloss i) (hW i).le
    nlinarith
  have hl : (∑ i, w i*(m-err i-2*pair i+(∑ j, if i ≤ j then loss j else 0))) ≤ final := by
    calc
      _ ≤ ∑ i, w i*final := Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left ((hlower i).trans (hfinal i)) (hw i))
      _ = final := by rw [← Finset.sum_mul,hws,one_mul]
  have he : (∑ i, w i*(m-err i-2*pair i+(∑ j, if i ≤ j then loss j else 0))) =
      m-(∑ i,w i*err i)-(∑ i,2*w i*pair i)+(∑ i,W i*loss i) := by
    simp only [mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib,
      weighted_suffix,←Finset.sum_mul,hws,one_mul]
    congr 2
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he] at hl
  have hs := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hp i)
  simp only [Finset.sum_add_distrib] at hs
  change m-(∑ i,w i*err i)-(∑ i,A*(w i)^2/(2*δ*W i))-(∑ i,W i*residual i) ≤ final
  linarith

lemma sum_succ_real (n : ℕ) :
    (∑ i ∈ Finset.range n, ((i:ℝ)+1)) = (n:ℝ)*((n:ℝ)+1)/2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ,ih]; push_cast; ring

lemma fin_prefix_succ {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j ≤ i then ((j:ℕ):ℝ)+1 else 0) =
      ((i:ℕ)+1:ℝ)*(((i:ℕ):ℝ)+2)/2 := by
  change (∑ j : Fin n, if (j:ℕ) ≤ (i:ℕ) then ((j:ℕ):ℝ)+1 else 0) = _
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => if j ≤ (i:ℕ) then (j:ℝ)+1 else 0)]
  have he : (∑ j ∈ Finset.range n, if j ≤ (i:ℕ) then (j:ℝ)+1 else 0) =
      ∑ j ∈ Finset.range ((i:ℕ)+1), ((j:ℝ)+1) := by
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp only [Finset.mem_filter,Finset.mem_range]
    omega
  rw [he,sum_succ_real]
  push_cast
  ring

lemma triangle_nonneg {n : ℕ} (i : Fin n) : 0 ≤ triangle i := by unfold triangle; positivity

lemma triangle_sum {n : ℕ} (hn : 0 < n) : (∑ i : Fin n, triangle i) = 1 := by
  simp only [triangle]
  rw [←Finset.sum_div,←Finset.mul_sum,Fin.sum_univ_eq_sum_range (fun j : ℕ => (j:ℝ)+1),sum_succ_real]
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  field_simp

lemma triangle_prefix {n : ℕ} (i : Fin n) :
    (∑ j : Fin n, if j ≤ i then triangle j else 0) =
      ((((i:ℕ):ℝ)+1)*(((i:ℕ):ℝ)+2))/((n:ℝ)*((n:ℝ)+1)) := by
  have he : ∀ j : Fin n, (if j ≤ i then triangle j else 0) =
      2*(if j ≤ i then ((j:ℕ):ℝ)+1 else 0)/((n:ℝ)*((n:ℝ)+1)) := by
    intro j
    by_cases h : j ≤ i <;> simp [triangle,h]
  simp_rw [he]
  rw [← Finset.sum_div,← Finset.mul_sum,fin_prefix_succ]
  ring

lemma triangle_prefix_pos {n : ℕ} (i : Fin n) : 0 < ∑ j : Fin n, if j ≤ i then triangle j else 0 := by
  rw [triangle_prefix]
  have hn : (0:ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt i.isLt)
  positivity

theorem triangle_remainder {n : ℕ} (hn : 0 < n) {A δ : ℝ}
    (hA : 0 ≤ A) (hδ : 0 < δ) :
    (∑ i : Fin n, A*(triangle i)^2/(2*δ*(∑ j : Fin n, if j ≤ i then triangle j else 0))) ≤
      2*A/(δ*(n:ℝ)) := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hh : ∀ i : Fin n,
      A*(triangle i)^2/(2*δ*(∑ j : Fin n, if j ≤ i then triangle j else 0)) ≤
        2*A/(δ*(n:ℝ)*((n:ℝ)+1)) := by
    intro i
    rw [triangle_prefix]
    dsimp [triangle]
    have hi : (0:ℝ) ≤ (i:ℕ) := Nat.cast_nonneg _
    field_simp
    nlinarith
  calc
    _ ≤ ∑ _i : Fin n, 2*A/(δ*(n:ℝ)*((n:ℝ)+1)) := Finset.sum_le_sum (fun i _ => hh i)
    _ = 2*A/(δ*((n:ℝ)+1)) := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)

open scoped RealInnerProductSpace
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem contraction_loss_lower (C : H →ₗ[ℝ] H) (eta g : H)
    (horth : ⟪eta,g⟫ = 0) (hg : ‖C g‖ ≤ ‖g‖) :
    ‖eta‖^2 - 2*⟪C eta,C (eta+g)⟫ ≤ ‖eta+g‖^2-‖C (eta+g)‖^2 := by
  have h0 := norm_add_sq_real eta g
  have h1 := norm_add_sq_real (C eta) (C g)
  rw [horth,mul_zero,add_zero] at h0
  have hcg : ‖C g‖^2 ≤ ‖g‖^2 := sq_le_sq₀ (norm_nonneg _) (norm_nonneg _) |>.mpr hg
  simp only [map_add,inner_add_right,real_inner_self_eq_norm_sq]
  nlinarith [sq_nonneg ‖C eta‖]

theorem finite_future_loss {n : ℕ} (hn : 0 < n)
    (partLoss energy loss residual err pair : Fin n → ℝ)
    (m final A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (henergy : ∀ i, 0 ≤ energy i)
    (hpair : ∀ i, (pair i)^2 ≤ A*energy i)
    (hloss : ∀ i, 2*δ*energy i ≤ loss i+residual i)
    (hinitial : ∀ i, m-err i-2*pair i ≤ partLoss i)
    (htelescope : ∀ i, partLoss i+(∑ j, if i ≤ j then loss j else 0) ≤ final) :
    m-(∑ i,triangle i*err i)-2*A/(δ*(n:ℝ))-
      (∑ i,(∑ j,if j ≤ i then triangle j else 0)*residual i) ≤ final := by
  have hh := weighted_leakage (triangle (n:=n)) (fun _ => final) err pair energy loss residual
    m final A δ hA hδ triangle_nonneg (triangle_sum hn) triangle_prefix_pos
    henergy hpair hloss (fun i => by linarith [hinitial i,htelescope i]) (fun _ => le_rfl)
  have ht := triangle_remainder hn hA hδ
  linarith

end

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
open scoped RealInnerProductSpace

lemma suffix_telescope (u : ℕ → ℝ) (m n : ℕ) :
    (∑ j ∈ Finset.range n,if m≤j then u j-u (j+1) else 0) =
      if m≤n then u m-u n else 0 := by
  induction n with
  | zero => by_cases hm : m=0 <;> simp [hm]
  | succ n ih =>
    rw [Finset.sum_range_succ,ih]
    by_cases hm : m≤n
    · simp only [ite_eq_left hm,ite_eq_left (show m≤n+1 by omega)]
      ring
    · by_cases he : m=n+1
      · subst m
        simp
      · simp [hm,show ¬m≤n+1 by omega]

lemma suffix_telescope_fin {n : ℕ} (u : ℕ → ℝ) (i : Fin n) :
    (∑ j : Fin n,if i ≤ j then u j-u (j+1) else 0) = u i-u n := by
  have hh := suffix_telescope u (i:ℕ) n
  rw [ite_eq_left (Nat.le_of_lt i.isLt)] at hh
  simpa only [Fin.le_iff_val_le_val] using
    ((Fin.sum_univ_eq_sum_range (fun j : ℕ => if (i:ℕ) ≤ j then u j-u (j+1) else 0) n).trans hh)

end Heisenberg.FiniteLeakage

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_MeanLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped Classical
open scoped Classical
open Filter Topology
open scoped Classical
open scoped Classical
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped Classical BigOperators
open scoped BigOperators Classical

namespace Heisenberg.FiniteLeakage

section
open scoped RealInnerProductSpace
variable {H Ω : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Fintype Ω]

lemma triangle_prefix_le_one {n : ℕ} (hn : 0<n) (i : Fin n) :
    (∑ j : Fin n,if j ≤ i then triangle j else 0) ≤ 1 := by
  rw [←triangle_sum hn]
  apply Finset.sum_le_sum
  intro j _
  split_ifs
  · exact le_rfl
  · exact triangle_nonneg j

end

open scoped RealInnerProductSpace
variable {Ω H : Type*} [Fintype Ω] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
lemma mean_square_le (μ : Ω → ℝ) (hμ : ∀ ω,0≤μ ω) (hs : ∑ ω,μ ω=1) (f : Ω → ℝ) :
    (∑ ω,μ ω*f ω)^2 ≤ ∑ ω,μ ω*(f ω)^2 := by
  let m : ℝ := ∑ ω,μ ω*f ω
  have hz : 0≤∑ ω,μ ω*(f ω-m)^2 := Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (sq_nonneg _))
  have he : (∑ ω,μ ω*(f ω-m)^2)=(∑ ω,μ ω*(f ω)^2)-m^2 := by
    have hterm (ω : Ω) : μ ω*(f ω-m)^2=μ ω*(f ω)^2-2*m*(μ ω*f ω)+m^2*μ ω := by ring
    simp_rw [hterm,Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum]
    rw [hs]
    change (∑ ω,μ ω*(f ω)^2)-2*m*m+m^2*1= _
    ring
  rw [he] at hz
  exact sub_nonneg.mp hz

theorem expected_ordered_leakage_moments
    (μ : Ω → ℝ) (hμ : ∀ ω,0≤μ ω) (hs : ∑ ω,μ ω=1)
    (P : Ω → ℕ → H →ₗ[ℝ] H) (n : ℕ) (hn : 0<n)
    (hP : ∀ ω j,j<n → ∀ v,‖P ω j v‖≤‖v‖)
    (eta : H) (g : Ω → H) (horth : ∀ ω,⟪eta,g ω⟫=0)
    (energy pair err : Ω → Fin n → ℝ) (A δ E B : ℝ)
    (hA : 0≤A) (hδ : 0<δ) (hB : 0≤B)
    (henergy : ∀ ω i,0≤energy ω i)
    (hpair : ∀ ω i,(pair ω i)^2≤A*energy ω i)
    (happrox : ∀ ω (i : Fin n),⟪P ω i eta,P ω i (eta+g ω)⟫≤err ω i+pair ω i)
    (hloss : ∀ i : Fin n, 2*δ*(∑ ω,μ ω*energy ω i) ≤
      (∑ ω,μ ω*(‖P ω i (eta+g ω)‖^2-‖P ω (i+1) (eta+g ω)‖^2))+B)
    (herr : ∀ i,∑ ω,μ ω*err ω i≤E) :
    ‖eta‖^2-2*E-2*A/(δ*(n:ℝ))-(n:ℝ)*B ≤
      ∑ ω,μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2) := by
  let u : ℕ → ℝ := fun j=>∑ ω,μ ω*‖P ω j (eta+g ω)‖^2
  let u₀ : ℝ := ∑ ω,μ ω*‖eta+g ω‖^2
  let q : Fin n → ℝ := fun i=>∑ ω,μ ω*pair ω i
  let e : Fin n → ℝ := fun i=>∑ ω,μ ω*energy ω i
  have hq (i : Fin n) : (q i)^2≤A*e i := by
    apply (mean_square_le μ hμ hs (fun ω=>pair ω i)).trans
    calc
      _ ≤ ∑ ω,μ ω*(A*energy ω i) := Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpair ω i) (hμ ω))
      _ = A*e i := by simp only [e,mul_left_comm (μ _) A,Finset.mul_sum]
  have he (i : Fin n) : 0≤e i := Finset.sum_nonneg (fun ω _ => mul_nonneg (hμ ω) (henergy ω i))
  have hp (i : Fin n) : ‖eta‖^2-2*E-2*q i≤u₀-u i := by
    have hpt (ω : Ω) : ‖eta‖^2-2*err ω i-2*pair ω i ≤
        ‖eta+g ω‖^2-‖P ω i (eta+g ω)‖^2 := by
      have h := contraction_loss_lower (P ω i) eta (g ω) (horth ω) (hP ω i i.isLt (g ω))
      linarith [happrox ω i]
    have ht := Finset.sum_le_sum (s:=Finset.univ) (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (hμ ω))
    simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul,hs,one_mul] at ht
    simp only [mul_left_comm (μ _) (2:ℝ),←Finset.mul_sum] at ht
    change ‖eta‖^2-2*(∑ ω,μ ω*err ω i)-2*q i≤u₀-u i at ht
    linarith [herr i]
  have hel (i : Fin n) : 2*δ*e i≤u i-u (i+1)+B := by
    simpa only [u,e,mul_sub,Finset.sum_sub_distrib] using hloss i
  have ht (i : Fin n) : (u₀-u i)+(∑ j : Fin n,if i≤j then u j-u (j+1) else 0)≤u₀-u n := by
    rw [suffix_telescope_fin]
    linarith
  have h := finite_future_loss hn (fun i=>u₀-u i) e (fun i=>u i-u (i+1))
    (fun _=>B) (fun _=>2*E) q (‖eta‖^2) (u₀-u n) A δ hA hδ he hq hel hp ht
  have her : (∑ i : Fin n,triangle i*(2*E))=2*E := by rw [←Finset.sum_mul,triangle_sum hn,one_mul]
  have hr : (∑ i : Fin n, (∑ j : Fin n, if j ≤ i then triangle j else 0) * B) ≤ (n : ℝ) * B := by
    calc
      _ ≤ ∑ _i : Fin n,B := Finset.sum_le_sum (fun i _ => mul_le_of_le_one_left hB (triangle_prefix_le_one hn i))
      _ = _ := by simp
  rw [her] at h
  have hf : u₀-u n=(∑ ω,μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2)) := by
    simp only [u₀,u,mul_sub,Finset.sum_sub_distrib]
  rw [←hf]
  linarith

end Heisenberg.FiniteLeakage

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SpatialFrame Heisenberg.Exposure
variable {k : ℕ}

theorem routed_mean_leakage (hk : 2 ≤ k) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ, ∃ C ≥ 0, ∀ (Ω I B : Type*) [Fintype Ω] [Fintype I]
      [Fintype B] [Nonempty B]
      (Λ F : Finset (ZSite k)) (H : Ω → ℕ → Set (Slots (B:=B) Λ))
      (x : I → ZSite k) (R : ℕ)
      (μ : Ω → ℝ) (eta : EuclideanSpace ℝ (Slots (B:=B) Λ))
      (g : Ω → EuclideanSpace ℝ (Slots (B:=B) Λ))
      (P : Ω → ℕ → EuclideanSpace ℝ (Slots (B:=B) Λ) →ₗ[ℝ]
        EuclideanSpace ℝ (Slots (B:=B) Λ))
      (K : Ω → ℕ → Slots (B:=B) Λ → I → ℝ)
      (a b : ℕ → Slots (B:=B) Λ) (q n : ℕ) (e : Fin q ≃ Edges Step Λ)
      (δ ρ ζ rem : ℝ),
      0 < n → 0 < δ → 0 ≤ rem →
      (∀ i : Fin q, a i = (e i).val.1) → (∀ i : Fin q, b i = (e i).val.2) →
      F ⊆ Λ → (∀ z ∈ F, ∀ w, Step z w → w ∈ Λ) →
      (∀ ω, 0 ≤ μ ω) → (∑ ω, μ ω = 1) →
      (∀ ω, ⟪eta,g ω⟫ = 0) →
      (∀ ω j, j < n → ∀ v, ‖P ω j v‖ ≤ ‖v‖) →
      (∀ ω (i : Fin n) j, j.1.val ∉ F → (P ω i (eta+g ω)).ofLp j = 0) →
      (∀ ω (i : Fin n) j, 0 ≤ (P ω i (eta+g ω)).ofLp j ∧
        (P ω i (eta+g ω)).ofLp j ≤ 1) →
      (∀ ω (i : Fin n) j l, 0 ≤ K ω i j l) →
      (∀ ω (i : Fin n) l, ∑ j, K ω i j l ≤ 1) →
      (∀ z r, 0 ≤ r → ((Finset.univ.filter (fun i => dist (x i) z ≤ r)).card : ℝ)
        ≤ L*(1+r)^((1:ℝ)/100)) →
      (∀ ω (i : Fin n) j l, K ω i j l ≠ 0 → j ∈ H ω i) →
      (∀ ω (i : Fin n), ⟪P ω i eta, P ω i (eta+g ω)⟫ =
        ∑ l, ∑ j, K ω i j l*(P ω i (eta+g ω)).ofLp j) →
      (∀ (i : Fin n) l, (∑ ω, μ ω*(if ¬Regular (blocked Λ (H ω i)) (x l) R M
        (1/(100*(k+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
      (∀ (i : Fin n) l, (∑ ω, μ ω*(∑ j, if (R:ℝ)<dist j.1.val (x l)
        then K ω i j l else 0)) ≤ ζ) →
      (∀ i : Fin n, 2*δ*(∑ ω, μ ω*quietEnergy (H ω i) a b q (P ω i (eta+g ω))) ≤
        (∑ ω, μ ω*(‖P ω i (eta+g ω)‖^2-‖P ω (i+1) (eta+g ω)‖^2))+rem) →
      ‖eta‖^2-2*((ρ+ζ)*Fintype.card I)-
        2*(C*(1+(R:ℝ))^((1:ℝ)/100)*Fintype.card I)/(δ*(n:ℝ))-(n:ℝ)*rem ≤
      ∑ ω, μ ω*(‖eta+g ω‖^2-‖P ω n (eta+g ω)‖^2) := by
  obtain ⟨M,C,hC,hroute⟩ := routed_sweep_pair hk L hL
  refine ⟨M,C,hC,?_⟩
  intro Ω I B _ _ _ _ Λ F H x R μ eta g P K a b q n e δ ρ ζ rem hn hδ hrem
    ha hb hF hframe hμ hs horth hP hsup hv hK hm hg hKH hrep hbad hesc hloss
  let energy : Ω → Fin n → ℝ := fun ω i => quietEnergy (H ω i) a b q (P ω i (eta+g ω))
  let pair : Ω → Fin n → ℝ := fun ω i => ∑ l, ∑ j,
    goodMass (K ω i) x (fun j => j.1.val) (blocked Λ (H ω i)) R M l j *
      (P ω i (eta+g ω)).ofLp j
  let err : Ω → Fin n → ℝ := fun ω i =>
    (∑ l, if ¬Regular (blocked Λ (H ω i)) (x l) R M (1/(100*(k+1:ℝ)))
      then (1:ℝ) else 0) +
    (∑ l, ∑ j, if (R:ℝ)<dist j.1.val (x l) then K ω i j l else 0)
  have he (ω : Ω) (i : Fin n) : 0 ≤ energy ω i := by
    apply Finset.sum_nonneg
    intro j _
    split_ifs
    · exact sq_nonneg _
    · rfl
  have hp (ω : Ω) (i : Fin n) : (pair ω i)^2 ≤
      (C*(1+(R:ℝ))^((1:ℝ)/100)*Fintype.card I)*energy ω i := by
    exact hroute I B Λ F (H ω i) x (K ω i) (P ω i (eta+g ω)) R a b q e ha hb
      hF hframe (hsup ω i) (hK ω i) (hm ω i) hg (hKH ω i) (fun j => (hv ω i j).1)
  have happ (ω : Ω) (i : Fin n) : ⟪P ω i eta,P ω i (eta+g ω)⟫ ≤ err ω i+pair ω i := by
    rw [hrep]
    exact kernel_pairing_split (K ω i) (hK ω i) (hm ω i) x (fun j => j.1.val)
      (blocked Λ (H ω i)) R M (P ω i (eta+g ω)).ofLp (hv ω i)
  have herr (i : Fin n) : (∑ ω, μ ω*err ω i) ≤ (ρ+ζ)*Fintype.card I := by
    simp only [err,mul_add (μ _) _ _,Finset.sum_add_distrib,Finset.mul_sum]
    conv_lhs => lhs; rw [Finset.sum_comm]
    conv_lhs => rhs; rw [Finset.sum_comm]
    have h₁ := Finset.sum_le_sum (s:=Finset.univ) (fun l _ => hbad i l)
    have h₂ := Finset.sum_le_sum (s:=Finset.univ) (fun l _ => hesc i l)
    simp only [Finset.mul_sum] at h₂
    calc
      _ ≤ (∑ _l : I, ρ)+(∑ _l : I, ζ) := add_le_add h₁ h₂
      _ = _ := by simp; ring
  exact Heisenberg.FiniteLeakage.expected_ordered_leakage_moments μ hμ hs P n hn hP eta g horth
    energy pair err (C*(1+(R:ℝ))^((1:ℝ)/100)*Fintype.card I) δ
    ((ρ+ζ)*Fintype.card I) rem (by positivity) hδ hrem he hp happ hloss herr

end Heisenberg.Flow

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_RoundEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open Module
open scoped Classical
open scoped Classical BigOperators
open scoped BigOperators Classical

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
open Heisenberg.MatrixContraction
variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
lemma euclideanMap_mul (A B : Matrix V V ℝ) (v : EuclideanSpace ℝ V) :
    euclideanMap (A*B) v = euclideanMap A (euclideanMap B v) := by
  ext i
  change ((A*B).mulVec v.ofLp) i = (A.mulVec (B.mulVec v.ofLp)) i
  rw [Matrix.mulVec_mulVec]

lemma substochastic_one : DoublySubstochastic (1 : Matrix V V ℝ) := by
  constructor
  · intro i j; simp only [Matrix.one_apply]; split_ifs <;> norm_num
  · intro i
    change (∑ j, if i=j then (1:ℝ) else 0)≤1
    simp
  · intro i
    change (∑ j, if j=i then (1:ℝ) else 0)≤1
    simp

lemma prefix_substochastic (K : ℕ → Matrix V V ℝ) (n : ℕ)
    (hK : ∀ i,i<n → DoublySubstochastic (K i)) : DoublySubstochastic (prefixMatrix K n) := by
  induction n with
  | zero => exact substochastic_one
  | succ n ih => exact (hK n (by omega)).mul (ih (fun i hi=>hK i (by omega)))

lemma prefix_add (K : ℕ → Matrix V V ℝ) (m n : ℕ) :
    prefixMatrix K (m+n)=prefixMatrix (fun i=>K (m+i)) n*prefixMatrix K m := by
  induction n with
  | zero => simp [prefixMatrix]
  | succ n ih =>
    change K (m+n)*prefixMatrix K (m+n)=(K (m+n)*prefixMatrix (fun i=>K (m+i)) n)*prefixMatrix K m
    rw [ih,Matrix.mul_assoc]

omit [DecidableEq V] in
lemma euclideanMap_bounds (A : Matrix V V ℝ) (hA : DoublySubstochastic A)
    (f : EuclideanSpace ℝ V) (hf : ∀ i,0≤f.ofLp i ∧ f.ofLp i≤1) :
    ∀ i,0≤(euclideanMap A f).ofLp i ∧ (euclideanMap A f).ofLp i≤1 := by
  intro i
  simp only [euclideanMap_apply,Matrix.mulVec,dotProduct]
  constructor
  · exact Finset.sum_nonneg (fun j _=>mul_nonneg (hA.nonneg i j) (hf j).1)
  · calc
      _ ≤ ∑ j,A i j*1 := Finset.sum_le_sum (fun j _=>mul_le_mul_of_nonneg_left (hf j).2 (hA.nonneg i j))
      _ ≤ 1 := by simpa using hA.row i

lemma pairing_columns (A : Matrix V V ℝ) (J : Finset V) (f : EuclideanSpace ℝ V) :
    ⟪euclideanMap A (WithLp.toLp 2 (fun j=>if j∈J then (1:ℝ) else 0)),f⟫ =
      ∑ j∈J,∑ i,A i j*f.ofLp i := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ i, f.ofLp i*(A.mulVec (fun j=>if j∈J then (1:ℝ) else 0) i))=_
  simp only [Matrix.mulVec,dotProduct,mul_ite,mul_one,mul_zero,
    Finset.sum_ite_mem,Finset.univ_inter,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

end Heisenberg.MeshPair

namespace Heisenberg.Exposure
open Heisenberg.MeshPair Heisenberg.MatrixContraction
variable {T V : Type*} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedSweep_prefix (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r n v =
      euclideanMap (prefixMatrix (fun i=>exposedStep s a b base P I p (r i)) n) v := by
  induction n with
  | zero => simp [exposedSweep,prefixMatrix]
  | succ n ih => rw [exposedSweep,prefixMatrix,euclideanMap_mul,ih]

omit [Fintype T] in
lemma exposedSweep_add (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (m n : ℕ)
    (v : EuclideanSpace ℝ V) :
    exposedSweep s a b base P I p r (m+n) v =
      exposedSweep s a b base P I p (fun i=>r (m+i)) n
        (exposedSweep s a b base P I p r m v) := by
  simp only [exposedSweep_prefix,prefix_add,euclideanMap_mul]

omit [Fintype T] in
lemma exposedSweep_bounds (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    (r : ℕ → T) (n : ℕ) (v : EuclideanSpace ℝ V)
    (hv : ∀ i,0≤v.ofLp i ∧ v.ofLp i≤1) :
    ∀ i,0≤(exposedSweep s a b base P I p r n v).ofLp i ∧
      (exposedSweep s a b base P I p r n v).ofLp i≤1 := by
  rw [exposedSweep_prefix]
  exact euclideanMap_bounds _ (prefix_substochastic _ n (fun i _=>
    exposedStep_substochastic s a b base P I p hp (r i))) v hv

omit [Fintype T] in
lemma exposedSweep_supported (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (v : EuclideanSpace ℝ V)
    (hv : ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I → v.ofLp j=0) :
    ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r n)∩I →
      (exposedSweep s a b base P I p r n v).ofLp j=0 := by
  cases n with
  | zero => exact hv
  | succ n =>
    intro j hj
    rw [hr n (by omega)] at hj
    exact residualBetween_supported _ _ _ _ _ _ _ _ j hj

end Heisenberg.Exposure

open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology
namespace Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]
lemma quietSweep_congr (H D : Set V) (a b c d : ℕ → V) (t : ℝ) (q : ℕ)
    (ha : ∀ i,i<q → a i=c i) (hb : ∀ i,i<q → b i=d i) (v : EuclideanSpace ℝ V) :
    quietSweep H D a b t q v=quietSweep H D c d t q v := by
  induction q with
  | zero => rfl
  | succ q ih => rw [quietSweep,quietSweep,ha q (by omega),hb q (by omega),
      ih (fun i hi=>ha i (by omega)) (fun i hi=>hb i (by omega))]
end Heisenberg.MeshPair
open scoped BigOperators Classical RealInnerProductSpace
open Filter Topology
namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {V : Type} [Fintype V]

theorem fixed_sweep_energy (a₀ b₀ : ℕ → V) (q : ℕ)
    (hab : ∀ i,i<q → a₀ i≠b₀ i) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → t≤2 →
      ∀ (T : Type) [Fintype T] (s : Equiv.Perm T) (a b : T → V) (r : ℕ → T),
      (∀ i,i<q → r (i+1)=s (r i)) →
      (∀ i,i<q → a (r i)=a₀ i) → (∀ i,i<q → b (r i)=b₀ i) →
      ∀ (p : T → ℝ) (_hp : ∀ i,0≤p i ∧ p i≤1) (_hrate : ∀ i,i<q → p (r i)=t/2)
        (P : Set (T×V)) (I : Set V) (v : (T → Bool) → EuclideanSpace ℝ V),
      (∀ base j,0≤(v base).ofLp j ∧ (v base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I →
        (v base).ofLp j=0) →
      (∑ base,layerMass s a b P p base *
        (t*MeshPair.quietEnergy (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0))
          a₀ b₀ q (v base))) ≤
        (∑ base,layerMass s a b P p base *
          (‖v base‖^2-‖exposedSweep s a b base P I p r q (v base)‖^2))+
        ε*t*Fintype.card V+t^2*q^2 := by
  filter_upwards [quietSweep_energy a₀ b₀ q hab hε] with t ht
  intro ht0 _ht2 T _ s a b r hr ha hb p hp hrate P I v hv hvI
  have hab' : ∀ i,i<q → a (r i)≠b (r i) := by
    intro i hi
    rw [ha i hi,hb i hi]
    exact hab i hi
  have hl (base : T → Bool) : t*MeshPair.quietEnergy
      (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)) a₀ b₀ q (v base) ≤
      ‖v base‖^2-‖exposedSweep s a b base P I p r q (v base)‖^2+
        ε*t*‖v base‖^2+(if ∃ i,i<q ∧ base (r i)=true then t*q else 0) := by
    have hc := exposedSweep_contraction s a b base P I p hp r q (v base)
    have hn : 0≤‖v base‖^2-‖exposedSweep s a b base P I p r q (v base)‖^2 := by
      nlinarith [norm_nonneg (v base),norm_nonneg (exposedSweep s a b base P I p r q (v base))]
    by_cases hnon : ∃ i,i<q ∧ base (r i)=true
    · rw [ite_eq_left hnon]
      have he := mul_le_mul_of_nonneg_left
        (quietEnergy_le_card (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0))
          a₀ b₀ q (v base) (hv base)) ht0
      have hz : 0≤ε*t*‖v base‖^2 := by positivity
      linarith
    · rw [ite_eq_right hnon]
      have hquiet : ∀ i,i<q → base (r i)=false := by
        intro i hi
        cases he : base (r i)
        · rfl
        · exact (hnon ⟨i,hi,he⟩).elim
      have heq := exposedSweep_coins s a b base P I p (fun _=>t/2) r q hrate (v base)
      rw [heq,exposedSweep_quiet s a b base P I r q t hr hquiet hab' (v base),
        quietSweep_congr _ _ (a ∘ r) (b ∘ r) a₀ b₀ t q ha hb]
      have he := (abs_le.mp (ht (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)) (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) (v base) (hvI base))).2
      rw [abs_of_nonneg ht0] at he
      linarith
  have hs := layerMass_sum s a b P p hp
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun base _=>
    mul_le_mul_of_nonneg_left (hl base) (layerMass_nonneg s a b P p hp base))
  have he : (∑ base,layerMass s a b P p base*(ε*t*‖v base‖^2))≤
      ε*t*Fintype.card V := by
    calc
      _ ≤ ∑ base,layerMass s a b P p base*(ε*t*Fintype.card V) :=
        Finset.sum_le_sum (fun base _=>mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (bounded_euclidean_sq (v base) (hv base)) (by positivity))
            (layerMass_nonneg s a b P p hp base))
      _ = _ := by rw [←Finset.sum_mul,hs,one_mul]
  have hn := tilted_nonquiet_error s a b P p hp r q ht0 hrate
  simp only [mul_add,Finset.sum_add_distrib] at h
  linarith

lemma exposedSweep_norm_antitone {T : Type} [Fintype T]
    (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (hp : ∀ j,0≤p j ∧ p j≤1)
    (r : ℕ → T) {m n : ℕ} (hmn : m≤n) (v : EuclideanSpace ℝ V) :
    ‖exposedSweep s a b base P I p r n v‖≤‖exposedSweep s a b base P I p r m v‖ := by
  obtain ⟨l,rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [exposedSweep_add]
  exact exposedSweep_contraction s a b base P I p hp _ _ _

theorem round_energy (a₀ b₀ : ℕ → V) (q : ℕ)
    (hab : ∀ j,j<q → a₀ j≠b₀ j) {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ t in 𝓝 (0:ℝ),0≤t → t≤2 →
      ∀ (T : Type) [Fintype T] (s : Equiv.Perm T) (a b : T → V)
        (r : ℕ → T) (c : ℕ → ℕ),
      (∀ j,r (j+1)=s (r j)) → (∀ i,c i+q≤c (i+1)) →
      (∀ i j,j<q → a (r (c i+j))=a₀ j) →
      (∀ i j,j<q → b (r (c i+j))=b₀ j) →
      ∀ (p : T → ℝ) (_hp : ∀ j,0≤p j ∧ p j≤1)
        (_hrate : ∀ i j,j<q → p (r (c i+j))=t/2)
        (P : Set (T×V)) (I : Set V) (f : (T → Bool) → EuclideanSpace ℝ V),
      (∀ base j,0≤(f base).ofLp j ∧ (f base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I →
        (f base).ofLp j=0) →
      ∀ i, t*(∑ base,layerMass s a b P p base *
        MeshPair.quietEnergy (holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i)))
          a₀ b₀ q (exposedSweep s a b base P I p r (c i) (f base))) ≤
        (∑ base,layerMass s a b P p base *
          (‖exposedSweep s a b base P I p r (c i) (f base)‖^2-
            ‖exposedSweep s a b base P I p r (c (i+1)) (f base)‖^2))+
        ε*t*Fintype.card V+t^2*q^2 := by
  filter_upwards [fixed_sweep_energy a₀ b₀ q hab hε] with t ht
  intro ht0 ht2 T _ s a b r c hr hc ha hb p hp hrate P I f hf hs i
  let v : (T → Bool) → EuclideanSpace ℝ V :=
    fun base=>exposedSweep s a b base P I p r (c i) (f base)
  have hv (base : T → Bool) : ∀ j,0≤(v base).ofLp j ∧ (v base).ofLp j≤1 :=
    exposedSweep_bounds s a b base P I p hp r (c i) (f base) (hf base)
  have hvI (base : T → Bool) : ∀ j,
      j∉holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i))∩I → (v base).ofLp j=0 :=
    exposedSweep_supported s a b base P I p r (c i) (fun j _=>hr j) (f base) (hs base)
  have hseg : ∀ j,j<q → r (c i+(j+1))=s (r (c i+j)) := by
    intro j _
    simpa only [Nat.add_assoc] using hr (c i+j)
  have h := ht ht0 ht2 T s a b (fun j=>r (c i+j)) hseg (ha i) (hb i)
    p hp (hrate i) P I v hv (by simpa only [Nat.add_zero] using hvI)
  simp only [Nat.add_zero] at h
  have hcolon (base : T → Bool) :
      ‖exposedSweep s a b base P I p (fun j=>r (c i+j)) q (v base)‖^2 ≥
        ‖exposedSweep s a b base P I p r (c (i+1)) (f base)‖^2 := by
    change ‖exposedSweep s a b base P I p (fun j=>r (c i+j)) q
      (exposedSweep s a b base P I p r (c i) (f base))‖^2≥_
    rw [←exposedSweep_add]
    exact pow_le_pow_left₀ (norm_nonneg _) (exposedSweep_norm_antitone s a b base P I p hp r (hc i) (f base)) 2
  rw [Finset.mul_sum]
  have hrew : (∑ base,layerMass s a b P p base*(t*MeshPair.quietEnergy
      (holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i))) a₀ b₀ q (v base)))=
      ∑ base,t*(layerMass s a b P p base*MeshPair.quietEnergy
      (holeCut s (fun j=>Equiv.swap (a j) (b j)) base P (r (c i))) a₀ b₀ q (v base)) := by
    apply Finset.sum_congr rfl
    intro base _
    ring
  rw [hrew] at h
  apply h.trans
  apply add_le_add _ (le_refl _)
  apply add_le_add _ (le_refl _)
  apply Finset.sum_le_sum
  intro base _
  exact mul_le_mul_of_nonneg_left (sub_le_sub_left (hcolon base) _) (layerMass_nonneg s a b P p hp base)

end Heisenberg.Exposure

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CyclicEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.MeshPair
variable {V : Type*} [Fintype V] [DecidableEq V]

lemma indicatorVector_sq (J : Finset V) : ‖indicatorVector J‖^2=(J.card:ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [indicatorVector]

lemma indicatorVector_orth (J : Finset V) (f : EuclideanSpace ℝ V)
    (hf : ∀ j∈J,f.ofLp j=1) : ⟪indicatorVector J,f-indicatorVector J⟫=0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j∈J
  · simp [indicatorVector,hj,hf j hj]
  · simp [indicatorVector,hj]

lemma euclideanMap_single (A : Matrix V V ℝ) (j k : V) :
    (euclideanMap A (WithLp.toLp 2 (Pi.single k (1:ℝ)))).ofLp j=A j k := by
  simp [euclideanMap_apply]

lemma indicatorVector_pairing (A : Matrix V V ℝ) (J : Finset V)
    (f : EuclideanSpace ℝ V) :
    ⟪euclideanMap A (indicatorVector J),f⟫=∑ j : J,∑ i,A i j.val*f.ofLp i := by
  rw [indicatorVector,pairing_columns]
  exact (Finset.sum_attach J (fun j=>∑ i,A i j*f.ofLp i)).symm

end Heisenberg.MeshPair
namespace Heisenberg.Exposure
open Heisenberg.MeshPair
variable {T V : Type} [Fintype T] [Fintype V] [DecidableEq V]

omit [Fintype T] in
lemma exposedPrefix_column_support
    (s : Equiv.Perm T) (a b : T → V) (base : T → Bool)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hr : ∀ i,i<n → r (i+1)=s (r i)) (k : V)
    (hk : k∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) :
    ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r n)∩I →
      prefixMatrix (fun i=>exposedStep s a b base P I p (r i)) n j k=0 := by
  have hs : ∀ j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I →
      (WithLp.toLp 2 (Pi.single k (1:ℝ)) : EuclideanSpace ℝ V).ofLp j=0 := by
    intro j hj
    have hjk : j≠k := fun he=>hj (he.symm ▸ hk)
    simp [hjk]
  have h := exposedSweep_supported s a b base P I p r n hr
    (WithLp.toLp 2 (Pi.single k (1:ℝ))) hs
  simpa only [exposedSweep_prefix,euclideanMap_single] using h

end Heisenberg.Exposure

open Filter Topology
open scoped RealInnerProductSpace Classical

open scoped Classical
open Filter
namespace Heisenberg.Serial

section
open Matrix Heisenberg.MeshPair
variable {V B : Type*} [Fintype V] [DecidableEq V] [Fintype B]

theorem mean_product (n : ℕ) (w : Fin n → B → ℝ)
    (K : Fin n → B → Matrix V V ℝ) :
    (∑ c : Fin n → B,(∏ i,w i (c i)) • product n (fun i => K i (c i))) =
      product n (fun i => ∑ b,w i b • K i b) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [Fintype.sum_equiv (split n) _
      (fun c => (w 0 c.1*(∏ i,w i.succ (c.2 i))) •
        (product n (fun i => K i.succ (c.2 i))*K 0 c.1))]
    · simp only [Fintype.sum_prod_type,product]
      have he (b : B) (c : Fin n → B) :
          (w 0 b*(∏ i,w i.succ (c i))) •
            (product n (fun i => K i.succ (c i))*K 0 b) =
          ((∏ i,w i.succ (c i)) • product n (fun i => K i.succ (c i)))*(w 0 b • K 0 b) := by
        rw [Matrix.smul_mul,Matrix.mul_smul,smul_smul,mul_comm]
      simp_rw [he,←Finset.sum_mul,ih,←Finset.mul_sum]
    · intro c
      rw [Fin.prod_univ_succ,product]
      rfl

lemma projection_mul (D E F : Set V) (σ : Equiv.Perm V) :
    killedBetween D E σ*projection F=killedBetween (D∩F) E σ := by
  ext i j
  simp only [Matrix.mul_apply,projection,killedBetween,Equiv.Perm.one_apply]
  rw [Finset.sum_eq_single j]
  · by_cases hj : j∈F <;> simp [hj,Set.mem_inter_iff]
  · intro k _ hkj
    simp [hkj]
  · simp

lemma walkKernel_succ (n : ℕ) (D : Fin (n+2) → Set V)
    (σ : Fin (n+1) → Equiv.Perm V) :
    walkKernel (n+1) D σ =
      walkKernel n (fun i => D i.succ) (fun i => σ i.succ)*killedBetween (D 0) (D 1) (σ 0) := by
  simp only [walkKernel,product,Matrix.mul_assoc,projection_mul,Set.inter_self,Fin.castSucc_zero,Fin.succ_zero_eq_one]
  congr 1
  have he : projection (D 1)*killedBetween (D 0) (D 1) (σ 0)=killedBetween (D 0) (D 1) (σ 0) := by
    ext i j
    simp only [Matrix.mul_apply,projection,killedBetween,Equiv.Perm.one_apply]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> simp_all
    · intro k _ hki
      simp [Ne.symm hki]
    · simp
  exact he.symm

theorem walkKernel_apply (n : ℕ) (D : Fin (n+1) → Set V)
    (σ : Fin n → Equiv.Perm V) (i j : V) :
    walkKernel n D σ i j = if survives n D σ j then
      if i=follow n σ j then 1 else 0 else 0 := by
  induction n generalizing i j with
  | zero =>
    simp only [walkKernel,product,one_mul,projection,killedBetween,follow,survives,Equiv.Perm.one_apply]
    by_cases hj : j∈D 0
    · by_cases hij : i=j
      · subst i; simp [hj]
      · simp [hj,hij]
    · simp [hj]
  | succ n ih =>
    rw [walkKernel_succ,Matrix.mul_apply,Finset.sum_eq_single (σ 0 j)]
    · rw [ih]
      simp only [killedBetween,follow,survives]
      have hs : survives n (fun i => D i.succ) (fun i => σ i.succ) (σ 0 j) → σ 0 j∈D 1 := by
        cases n <;> simp +contextual [survives]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [killedBetween,hk]
    · simp

end

open Matrix Heisenberg.Hitting

end Heisenberg.Serial

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_HistoryMarginals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter

open scoped BigOperators Classical

namespace Heisenberg.Exposure
variable {I J B : Type*} [Fintype I] [Fintype J] [Fintype B]

theorem product_marginal (w : I → B → ℝ) (hw : ∀ i,∑ b,w i b=1)
    (r : J → I) (hr : Function.Injective r) (F : (J → B) → ℝ) :
    (∑ c : I → B,productWeight w c*F (c ∘ r)) =
      ∑ c : J → B,productWeight (fun j => w (r j)) c * F c := by
  let M : I → Prop := fun i => i∈Set.range r
  let e : J ≃ {i // M i} := Equiv.ofInjective r hr
  let q := Equiv.piEquivPiSubtypeProd M (fun _ => B)
  rw [←q.symm.sum_comp,Fintype.sum_prod_type]
  have he (a : {i // M i} → B) (b : {i // ¬M i} → B) :
      q.symm (a,b) ∘ r = a ∘ e := by
    funext j
    exact merge_left M a b (e j)
  simp only [he]
  change (∑ a,∑ b,productWeight w (merge M a b)*F (a ∘ e))=_
  simp_rw [productWeight_merge,mul_right_comm _ _ (F _),←Finset.mul_sum]
  have hs : (∑ b : {i // ¬M i} → B,
      productWeight (fun i : {i // ¬M i} => w i) b)=1 :=
    by simp only [productWeight, ←Fintype.prod_sum, hw, Finset.prod_const_one]
  simp only [hs,mul_one]
  let e' : ({i // M i} → B) ≃ (J → B) := Equiv.piCongrLeft (fun _ => B) e.symm
  rw [←e'.sum_comp]
  apply Finset.sum_congr rfl
  intro a _
  have hf : e' a=a ∘ e := by
    funext j
    simp [e', Equiv.piCongrLeft_apply]
  rw [hf]
  congr 1
  unfold productWeight
  convert (e.prod_comp (fun i => w i (a i))).symm using 1
  · congr 1
    ext j
    simp
  · apply Finset.prod_congr rfl
    intro j _
    rfl

end Heisenberg.Exposure

namespace Heisenberg.Serial

section
open Heisenberg.Exposure Heisenberg.MeshPair
variable {V B I : Type*} [Fintype V] [DecidableEq V] [Fintype B] [Fintype I]

theorem mean_walkKernel (n : ℕ) (w : Fin n → B → ℝ)
    (D : Fin (n+1) → Set V) (σ : Fin n → B → Equiv.Perm V) :
    (∑ c : Fin n → B,(productWeight w c) • walkKernel n D (fun i => σ i (c i))) =
      product n (fun i => ∑ b,w i b • killedBetween (D i.castSucc) (D i.succ) (σ i b)) *
        projection (D 0) := by
  simp only [walkKernel, ←Matrix.smul_mul, ←Finset.sum_mul]
  congr 1
  exact mean_product n w (fun i b => killedBetween (D i.castSucc) (D i.succ) (σ i b))

theorem prefix_mean (n : ℕ) (w : I → B → ℝ) (hw : ∀ i,∑ b,w i b=1)
    (r : Fin n → I) (hr : Function.Injective r) (D : Fin (n+1) → Set V)
    (σ : Fin n → B → Equiv.Perm V) (x y : V) :
    (∑ c : I → B,productWeight w c * walkKernel n D (fun i => σ i (c (r i))) x y) =
      (product n (fun i => ∑ b,w (r i) b • killedBetween (D i.castSucc) (D i.succ) (σ i b)) *
        projection (D 0)) x y := by
  have h := product_marginal w hw r hr
    (fun c => walkKernel n D (fun i => σ i (c i)) x y)
  change (∑ c,productWeight w c * (fun c => walkKernel n D (fun i => σ i (c i)) x y) (c ∘ r)) = _
  rw [h]
  have he := congrArg (fun A : Matrix V V ℝ => A x y)
    (mean_walkKernel n (fun i => w (r i)) D σ)
  simp only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul] at he
  convert he using 1
  congr 1
  ext c
  simp

theorem prefix_endpoint_bound (n : ℕ) (w : I → B → ℝ)
    (hw : ∀ i,∑ b,w i b=1) (hw0 : ∀ i b,0≤w i b)
    (r : Fin n → I) (hr : Function.Injective r) (D : Fin (n+1) → Set V)
    (σ : Fin n → B → Equiv.Perm V) (j : V) (A : Set V) :
    (∑ i,if i∈A then
      (product n (fun k => ∑ b,w (r k) b • killedBetween (D k.castSucc) (D k.succ) (σ k b)) *
        projection (D 0)) i j else 0) ≤
      ∑ c : I → B,if follow n (fun k => σ k (c (r k))) j∈A then productWeight w c else 0 := by
  simp_rw [←prefix_mean n w hw r hr D σ]
  have hf (i : V) : (if i∈A then ∑ c,productWeight w c * walkKernel n D (fun k => σ k (c (r k))) i j else 0) =
      ∑ c,productWeight w c * (if i∈A then walkKernel n D (fun k => σ k (c (r k))) i j else 0) := by
    by_cases hi : i∈A <;> simp [hi]
  simp only [hf]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro c _
  rw [←Finset.mul_sum]
  have hn := productWeight_nonneg w hw0 c
  simp only [walkKernel_apply]
  by_cases hs : survives n D (fun k => σ k (c (r k))) j
  · simp only [hs,ite_true]
    rw [Finset.sum_eq_single (follow n (fun k => σ k (c (r k))) j)]
    · by_cases ha : follow n (fun k => σ k (c (r k))) j∈A <;> simp [ha]
    · intro i _ hi
      simp [hi]
    · simp
  · simp only [hs,ite_false,ite_self,Finset.sum_const_zero,mul_zero]
    split_ifs <;> positivity

end

open Heisenberg.Exposure
variable {V : Type*}

lemma follow_snoc (n : ℕ) (σ : Fin (n+1) → Equiv.Perm V) (v : V) :
    follow (n+1) σ v=σ (Fin.last n) (follow n (fun i=>σ i.castSucc) v) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [follow,ih]
    rfl

lemma follow_trajectory (τ : ℕ → Equiv.Perm V) (c : ℕ → Bool) (n : ℕ) (v : V) :
    follow n (fun i => if c i then τ i else 1) v=trajectory τ c n v := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [follow_snoc]
    change (if c n then τ n else 1) (follow n (fun i => if c i then τ i else 1) v) = _
    rw [ih,trajectory_succ]
    split_ifs <;> rfl

end Heisenberg.Serial

open scoped BigOperators Classical

open scoped BigOperators Classical
namespace Heisenberg.Clocks

lemma shifted_strictMono {n r : ℕ} (f : WeakTimes n r) : StrictMono (shifted f) := by
  intro i j hij
  have h := f.property hij.le
  have h' : (f.val i).val ≤ (f.val j).val := h
  change (f.val i).val+i.val < (f.val j).val+j.val
  have hij' : i.val < j.val := hij
  omega

lemma timeSet_card {n r : ℕ} (f : WeakTimes n r) : (timeSet f).card = r := by
  rw [timeSet,Finset.card_image_of_injective _ (shifted_strictMono f).injective]
  simp

lemma timeSet_injective {n r : ℕ} : Function.Injective (timeSet (n:=n) (r:=r)) := by
  intro f g he
  have hr : Set.range (shifted f) = Set.range (shifted g) := by
    have hh := congrArg (fun s : Finset (Fin (n+r)) => (s : Set (Fin (n+r)))) he
    simpa only [timeSet,Finset.coe_image,Finset.coe_univ,Set.image_univ] using hh
  have hf := ((shifted_strictMono f).range_inj (shifted_strictMono g)).mp hr
  apply Subtype.ext
  funext i
  have hh := congrArg (fun f : Fin r → Fin (n+r) => (f i).val) hf
  apply Fin.ext
  change (f.val i).val+i.val = (g.val i).val+i.val at hh
  omega

theorem card_weakTimes_le (n r : ℕ) : Fintype.card (WeakTimes n r) ≤ (n+r).choose r := by
  let e : WeakTimes n r → {s : Finset (Fin (n+r)) // s ∈ Finset.univ.powersetCard r} :=
    fun f => ⟨timeSet f,Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,timeSet_card f⟩⟩
  have he : Function.Injective e := fun f g h => timeSet_injective (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective e he
  simpa only [Fintype.card_coe,Finset.card_powersetCard,Finset.card_univ,Fintype.card_fin] using hc

variable {X E : Type*}

lemma mem_edgeWords_cons (choices : X → Finset E) (next : X → E → X) (r : ℕ)
    (x : X) (e : E) (l : List E) :
    e::l ∈ edgeWords choices next (r+1) x ↔
      e ∈ choices x ∧ l ∈ edgeWords choices next r (next x e) := by
  simp [edgeWords]

lemma card_edgeWords (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r : ℕ) (x : X) :
    (edgeWords choices next r x).card ≤ B^r := by
  induction r generalizing x with
  | zero => simp [edgeWords]
  | succ r ih =>
    calc
      _ ≤ ∑ e ∈ choices x, ((edgeWords choices next r (next x e)).image (List.cons e)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ _e ∈ choices x,B^r := Finset.sum_le_sum (fun e _ => (Finset.card_image_le).trans (ih _))
      _ = (choices x).card*B^r := by simp
      _ ≤ B*B^r := Nat.mul_le_mul_right _ (hB x)
      _ = _ := (pow_succ' _ _).symm

lemma follows_mem (choices : X → Finset E) (next : X → E → X) (x : X) (l : List E)
    (hl : Follows choices next x l) : l ∈ edgeWords choices next l.length x := by
  induction l generalizing x with
  | nil => simp [edgeWords]
  | cons e l ih => exact (mem_edgeWords_cons choices next l.length x e l).mpr ⟨hl.1,ih _ hl.2⟩

end Heisenberg.Clocks

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ClockWitnesses
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace Heisenberg.Clocks

section
variable {X E I : Type*} [Fintype E]

lemma weakTimes_card (r N : ℕ) : (weakTimes r N).card ≤ (N+r).choose r := by
  rw [weakTimes,←Fintype.card_subtype]
  exact card_weakTimes_le N r

lemma card_functionWords (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r : ℕ) (x : X) :
    (functionWords choices next r x).card ≤ B^r := by
  apply le_trans _ (card_edgeWords choices next B hB r x)
  apply Finset.card_le_card_of_injOn (fun w => List.ofFn w)
  · intro w hw; exact (Finset.mem_filter.mp hw).2
  · intro a _ b _ he
    exact List.ofFn_inj.mp he

lemma witnessMarks_card (choices : X → Finset E) (next : X → E → X) (r N : ℕ) (x : X)
    (index : Fin N → E → Bool → I) (q) (hq : q ∈ witnesses choices next r N x index) :
    (witnessMarks index q).card = r := by
  have hi := (Finset.mem_filter.mp hq).2
  rw [witnessMarks,Finset.card_image_of_injective _ hi,Finset.card_univ,Fintype.card_fin]

lemma witnesses_card (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r N : ℕ) (x : X) (index : Fin N → E → Bool → I) :
    (witnesses choices next r N x index).card ≤ (N+r).choose r * (2*B)^r := by
  calc
    _ ≤ ((weakTimes r N).product ((functionWords choices next r x).product Finset.univ)).card :=
      Finset.card_filter_le _ _
    _ = (weakTimes r N).card * ((functionWords choices next r x).card * 2^r) := by
      simp
    _ ≤ (N+r).choose r * (B^r * 2^r) :=
      Nat.mul_le_mul (weakTimes_card r N) (Nat.mul_le_mul_right _ (card_functionWords choices next B hB r x))
    _ = _ := by rw [←Nat.mul_pow,Nat.mul_comm B 2]

end

variable {X E I : Type*}

lemma moveList_bounds (x : ℕ → X) (m n : ℕ) {j : ℕ} (hj : j ∈ moveList x m n) :
    m ≤ j ∧ j < m+n := by
  induction n generalizing m with
  | zero => simp [moveList] at hj
  | succ n ih =>
    simp only [moveList] at hj
    split_ifs at hj with he
    · obtain ⟨h₁,h₂⟩ := ih (m+1) hj
      omega
    · rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · obtain ⟨h₁,h₂⟩ := ih (m+1) hj
        omega

lemma moveList_moved (x : ℕ → X) (m n : ℕ) {j : ℕ} (hj : j ∈ moveList x m n) :
    x (j+1) ≠ x j := by
  induction n generalizing m with
  | zero => simp [moveList] at hj
  | succ n ih =>
    simp only [moveList] at hj
    split_ifs at hj with he
    · exact ih (m+1) hj
    · rcases List.mem_cons.mp hj with rfl | hj
      · exact he
      · exact ih (m+1) hj

lemma moveList_pairwise (x : ℕ → X) (m n : ℕ) :
    (moveList x m n).Pairwise (· < ·) := by
  induction n generalizing m with
  | zero => simp [moveList]
  | succ n ih =>
    simp only [moveList]
    split_ifs
    · exact ih _
    · exact List.pairwise_cons.mpr ⟨fun j hj => by
        have h := (moveList_bounds x (m+1) n hj).1
        omega, ih _⟩

lemma moveList_follows (choices : X → Finset E) (next : X → E → X)
    (x : ℕ → X) (e : ℕ → E) (m n : ℕ)
    (hmove : ∀ j,m ≤ j → j < m+n → x (j+1) ≠ x j →
      e j ∈ choices (x j) ∧ x (j+1)=next (x j) (e j)) :
    Follows choices next (x m) ((moveList x m n).map e) := by
  induction n generalizing m with
  | zero => trivial
  | succ n ih =>
    simp only [moveList]
    split_ifs with he
    · rw [←he]
      exact ih (m+1) (fun j h₁ h₂ => hmove j (by omega) (by omega))
    · have hm := hmove m le_rfl (by omega) he
      change e m ∈ choices (x m) ∧ _
      refine ⟨hm.1,?_⟩
      rw [←hm.2]
      exact ih (m+1) (fun j h₁ h₂ => hmove j (by omega) (by omega))

lemma follows_take (choices : X → Finset E) (next : X → E → X)
    (x : X) (l : List E) (hl : Follows choices next x l) (r : ℕ) :
    Follows choices next x (l.take r) := by
  induction r generalizing x l with
  | zero => trivial
  | succ r ih =>
    cases l with
    | nil => trivial
    | cons e l => exact ⟨hl.1,ih _ _ hl.2⟩

lemma dist_le_moves [PseudoMetricSpace X] (x : ℕ → X) (m n : ℕ)
    (hstep : ∀ j,m ≤ j → j < m+n → dist (x j) (x (j+1)) ≤ 1) :
    dist (x m) (x (m+n)) ≤ (moveList x m n).length := by
  induction n generalizing m with
  | zero => simp [moveList]
  | succ n ih =>
    have ht := ih (m+1) (fun j h₁ h₂ => hstep j (by omega) (by omega))
    have hh : m+(n+1)=(m+1)+n := by omega
    rw [moveList]
    split_ifs with he
    · rw [←he,hh]
      exact ht
    · rw [List.length_cons,Nat.cast_add,Nat.cast_one,hh]
      exact (dist_triangle _ (x (m+1)) _).trans (by linarith [hstep m le_rfl (by omega)])

end Heisenberg.Clocks

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ClockInsertions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical

namespace Heisenberg.Bernoulli
variable {I Q : Type*} [Fintype I]
theorem marked_union_bound_on (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
    (hκ : ∀ i,1 ≤ κ i) (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (q : Finset Q) (marks : Q → Finset I) (r : ℕ) (hm : ∀ x ∈ q,(marks x).card = r)
    (δ : ℝ) (_hδ : 0 ≤ δ) (hrate : ∀ x ∈ q,∀ i ∈ marks x,κ i*p i ≤ δ)
    (event : (I → Bool) → Prop)
    (hcover : ∀ c,event c → ∃ x ∈ q,∀ i ∈ marks x,c i = true) :
    (∑ c,if event c then weight p c*W c else 0) ≤
      (q.card:ℝ)*δ^r*(∑ c,weight p c*W c) := by
  have hb (c : I → Bool) : (if event c then (1:ℝ) else 0) ≤ ∑ x ∈ q,test (marks x) c := by
    by_cases hc : event c
    · obtain ⟨x,hx,hm⟩ := hcover c hc
      rw [ite_eq_left hc]
      have he : test (marks x) c = 1 := ite_eq_left hm
      rw [←he]
      exact Finset.single_le_sum (fun x _ => test_nonneg _ c) hx
    · rw [ite_eq_right hc]
      exact Finset.sum_nonneg (fun x _ => test_nonneg _ c)
  have hZ : 0 ≤ ∑ c,weight p c*W c :=
    Finset.sum_nonneg (fun c _ => mul_nonneg (weight_nonneg p hp c) (hW c))
  calc
    _ = ∑ c,weight p c*W c*(if event c then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro c _
      split_ifs <;> simp
    _ ≤ ∑ c,weight p c*W c*(∑ x ∈ q,test (marks x) c) :=
      Finset.sum_le_sum (fun c _ => mul_le_mul_of_nonneg_left (hb c) (mul_nonneg (weight_nonneg p hp c) (hW c)))
    _ = ∑ x ∈ q,∑ c,weight p c*(W c*test (marks x) c) := by
      simp only [Finset.mul_sum,mul_assoc]
      rw [Finset.sum_comm]
    _ ≤ ∑ x ∈ q,δ^r*(∑ c,weight p c*W c) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (factorial_bound_rates p κ hp hκ W hW hins (marks x)).trans
      apply mul_le_mul_of_nonneg_right _ hZ
      calc
        _ ≤ ∏ _i ∈ marks x,δ := Finset.prod_le_prod (fun i _ => mul_nonneg (by linarith [hκ i]) (hp i).1) (fun i hi => hrate x hx i hi)
        _ = δ^r := by rw [Finset.prod_const,hm x hx]
    _ = _ := by simp [mul_assoc]

end Heisenberg.Bernoulli

namespace Heisenberg.Clocks
variable {X E I : Type*} [Fintype E]
theorem witness_probability_spatial [Fintype I]
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (r N : ℕ) (x : X) (index : Fin N → E → Bool → I)
    (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (hκ : ∀ i,1 ≤ κ i)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (δ : ℝ) (hδ : 0 ≤ δ) (hrate : ∀ t e b,κ (index t e b)*p (index t e b) ≤ δ)
    (event : (I → Bool) → Prop)
    (hcover : ∀ c,event c → ∃ q ∈ witnesses choices next r N x index,
      ∀ k : Fin r,c (index (q.1 k) (q.2.1 k) (q.2.2 k)) = true) :
    (∑ c,if event c then Bernoulli.weight p c*W c else 0) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ)*δ)^r * (∑ c,Bernoulli.weight p c*W c) := by
  have hc : ∀ c,event c → ∃ q ∈ witnesses choices next r N x index,
      ∀ i ∈ witnessMarks index q,c i=true := by
    intro c he
    obtain ⟨q,hq,hh⟩ := hcover c he
    refine ⟨q,hq,?_⟩
    intro i hi
    obtain ⟨k,_hk,rfl⟩ := Finset.mem_image.mp hi
    exact hh k
  have hb := Bernoulli.marked_union_bound_on p κ hp hκ W hW hins
    (witnesses choices next r N x index) (witnessMarks index) r
    (fun q hq => witnessMarks_card choices next r N x index q hq) δ hδ (by
      intro q _ i hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      exact hrate _ _ _) event hc
  have hZ : 0 ≤ ∑ c,Bernoulli.weight p c*W c := Finset.sum_nonneg
    (fun c _ => mul_nonneg (Bernoulli.weight_nonneg p hp c) (hW c))
  apply hb.trans
  have hn : ((witnesses choices next r N x index).card:ℝ) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ))^r := by
    exact_mod_cast witnesses_card choices next B hB r N x index
  calc
    _ ≤ (((N+r).choose r:ℝ)*(2*(B:ℝ))^r)*δ^r*(∑ c,Bernoulli.weight p c*W c) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hn (pow_nonneg hδ _)) hZ
    _ = _ := by rw [mul_assoc _ _ (δ^r),←mul_pow]

theorem adaptive_trajectory_witness (choices : X → Finset E) (next : X → E → X)
    (x : ℕ → X) (edge : ℕ → E) (r n N : ℕ)
    (time : ℕ → Fin N) (src : ℕ → Bool) (index : Fin N → E → Bool → I)
    (c : I → Bool) (hlen : r ≤ (moveList x 0 n).length)
    (htime : Monotone time)
    (hinj : Set.InjOn (fun j => index (time j) (edge j) (src j)) {j | j<n ∧ x (j+1)≠x j})
    (hmove : ∀ j,j<n → x (j+1)≠x j →
      edge j ∈ choices (x j) ∧ x (j+1)=next (x j) (edge j) ∧
      c (index (time j) (edge j) (src j))=true) :
    ∃ q ∈ witnesses choices next r N (x 0) index,
      ∀ k : Fin r,c (index (q.1 k) (q.2.1 k) (q.2.2 k))=true := by
  let l := (moveList x 0 n).take r
  have hl : l.length=r := by simp [l,List.length_take,Nat.min_eq_left hlen]
  let j : Fin r → ℕ := fun k => l.get (Fin.cast hl.symm k)
  have hjmem (k : Fin r) : j k ∈ moveList x 0 n :=
    List.mem_of_mem_take (List.get_mem l _)
  have hjlt (k : Fin r) : j k<n := by simpa using (moveList_bounds x 0 n (hjmem k)).2
  have hjmove (k : Fin r) := hmove (j k) (hjlt k) (moveList_moved x 0 n (hjmem k))
  have hjmono : StrictMono j := by
    intro a b hab
    have hh : l.Pairwise (· < ·) := (moveList_pairwise x 0 n).take
    exact List.pairwise_iff_get.mp hh _ _ (by simpa using hab)
  have hof : List.ofFn j = l := by
    rw [←List.ofFn_congr hl (List.get l)]
    exact List.ofFn_get l
  let q : (Fin r → Fin N) × (Fin r → E) × (Fin r → Bool) :=
    (fun k => time (j k),fun k => edge (j k),fun k => src (j k))
  refine ⟨q,?_,fun k => (hjmove k).2.2⟩
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htime.comp hjmono.monotone⟩
    · apply Finset.mem_product.mpr
      refine ⟨?_,Finset.mem_univ _⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,?_⟩
      have hf := moveList_follows choices next x edge 0 n
        (fun j _ hj hm => ⟨(hmove j (by simpa using hj) hm).1,(hmove j (by simpa using hj) hm).2.1⟩)
      have ht := follows_take choices next (x 0) _ hf r
      have he : List.ofFn (fun k : Fin r => edge (j k)) = l.map edge := by
        change List.ofFn (edge ∘ j) = _
        rw [←List.map_ofFn,hof]
      rw [he]
      convert follows_mem choices next (x 0) (l.map edge) (by simpa [l,List.map_take] using ht) using 1
      simp [hl]
  · intro a b he
    apply hjmono.injective
    exact hinj ⟨hjlt a,moveList_moved x 0 n (hjmem a)⟩ ⟨hjlt b,moveList_moved x 0 n (hjmem b)⟩ he

theorem adaptive_trajectory_probability [Fintype I] [PseudoMetricSpace X]
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card ≤ B) (v : X)
    (x : (I → Bool) → ℕ → X) (hx0 : ∀ c,x c 0=v)
    (edge : ℕ → E) (n N r : ℕ) (time : ℕ → Fin N)
    (index : Fin N → E → Bool → I) (src : (I → Bool) → ℕ → Bool)
    (htime : Monotone time)
    (hinj : ∀ c,Set.InjOn (fun j => index (time j) (edge j) (src c j))
      {j | j<n ∧ x c (j+1)≠x c j})
    (hstep : ∀ c j,j<n → dist (x c j) (x c (j+1)) ≤ 1)
    (hmove : ∀ c j,j<n → x c (j+1)≠x c j →
      edge j ∈ choices (x c j) ∧ x c (j+1)=next (x c j) (edge j) ∧
      c (index (time j) (edge j) (src c j))=true)
    (p κ : I → ℝ) (hp : ∀ i,0 ≤ p i ∧ p i ≤ 1) (hκ : ∀ i,1 ≤ κ i)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0 ≤ W c)
    (hins : ∀ c i,W (Function.update c i true) ≤ κ i*W (Function.update c i false))
    (δ : ℝ) (hδ : 0 ≤ δ) (hrate : ∀ t e b,κ (index t e b)*p (index t e b) ≤ δ) :
    (∑ c,if (r:ℝ) ≤ dist v (x c n) then Bernoulli.weight p c*W c else 0) ≤
      ((N+r).choose r:ℝ)*(2*(B:ℝ)*δ)^r * (∑ c,Bernoulli.weight p c*W c) := by
  apply witness_probability_spatial choices next B hB r N v index p κ hp hκ W hW hins δ hδ hrate
  intro c hc
  have hd := dist_le_moves (x c) 0 n (fun j _ hj => hstep c j (by simpa using hj))
  have hd' : dist v (x c n) ≤ ((moveList (x c) 0 n).length:ℝ) := by simpa [hx0 c] using hd
  have hlen : r ≤ (moveList (x c) 0 n).length := by
    have hh : (r:ℝ) ≤ ((moveList (x c) 0 n).length:ℝ) := hc.trans hd'
    exact_mod_cast hh
  simpa only [hx0 c] using adaptive_trajectory_witness choices next (x c) edge r n N time (src c) index c
    hlen htime (hinj c) (hmove c)

end Heisenberg.Clocks

namespace Heisenberg.Bernoulli
variable {I : Type*} [Fintype I]

lemma weight_total (p : I → ℝ) : ∑ c, weight p c=1 := by
  classical
  unfold weight
  rw [←Fintype.prod_sum (fun i (b : Bool) => if b then p i else 1-p i)]
  simp

lemma double_weight (p : I → ℝ) (c : I ⊕ I → Bool) :
    weight (doubleRates p) c=weight p (original c)*weight p (fresh c) := by
  classical
  simp only [weight,Fintype.prod_sum_type,doubleRates,original,fresh,Function.comp_apply,Sum.elim_inl,Sum.elim_inr]
  congr 1

lemma double_sum (p : I → ℝ) (F : (I → Bool) → (I → Bool) → ℝ) :
    (∑ c : I ⊕ I → Bool,weight (doubleRates p) c*F (original c) (fresh c)) =
      ∑ b : I → Bool,∑ f : I → Bool,weight p b*weight p f*F b f := by
  rw [←(Equiv.sumArrowEquivProdArrow I I Bool).symm.sum_comp]
  simp only [double_weight,Fintype.sum_prod_type]
  rfl

lemma double_partition (p : I → ℝ) (W : (I → Bool) → ℝ) :
    (∑ c : I ⊕ I → Bool,weight (doubleRates p) c*W (original c)) =
      ∑ b : I → Bool,weight p b*W b := by
  rw [double_sum p (fun b _ => W b)]
  simp_rw [mul_right_comm _ _ (W _),←Finset.mul_sum,weight_total,mul_one]

omit [Fintype I] in
lemma original_update_left (c : I ⊕ I → Bool) (i : I) (b : Bool) :
    original (Function.update c (Sum.inl i) b)=Function.update (original c) i b := by
  classical
  funext j
  by_cases hj : j=i
  · subst j; simp [original]
  · simp [original,hj]

omit [Fintype I] in
lemma original_update_right (c : I ⊕ I → Bool) (i : I) (b : Bool) :
    original (Function.update c (Sum.inr i) b)=original c := by
  classical
  funext j
  simp [original]

omit [Fintype I] in

theorem double_insertion {κ : ℝ} (W : (I → Bool) → ℝ)
    (h : ∀ c i,W (Function.update c i true)≤κ*W (Function.update c i false)) :
    ∀ (c : I ⊕ I → Bool) i,
      W (original (Function.update c i true)) ≤
        (Sum.elim (fun _ => κ) (fun _ => (1:ℝ)) i)*W (original (Function.update c i false)) := by
  intro c i
  cases i with
  | inl i => simpa only [original_update_left,Sum.elim_inl] using h (original c) i
  | inr i => simp only [original_update_right,Sum.elim_inr,one_mul,le_refl]

end Heisenberg.Bernoulli

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_SpatialClocks
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace Classical
open scoped Classical
open Filter
open scoped BigOperators Classical

namespace Heisenberg.Clocks
open Heisenberg.Exposure Heisenberg.Bernoulli
variable {V X E I : Type*} [PseudoMetricSpace X] [Fintype E] [Fintype I]

omit [PseudoMetricSpace X] [Fintype E] [Fintype I] in
lemma mixedCoins_index (M : (I → Bool) → I → Prop) (c : I ⊕ I → Bool) (r : ℕ → I) (j : ℕ) :
    mixedCoins M c r j=c (if mixedSource M c r j then Sum.inl (r j) else Sum.inr (r j)) := by
  simp only [mixedCoins,mixedSource,decide_eq_true_eq]
  split_ifs <;> rfl

theorem joint_trajectory_localization
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card≤B)
    (τ : ℕ → Equiv.Perm V) (site : V → X) (v : V)
    (r : ℕ → I) (n N R : ℕ) (hr : Set.InjOn r (Set.Iio n))
    (edge : ℕ → E) (time : ℕ → Fin N) (index : Fin N → E → Bool → I ⊕ I)
    (htime : Monotone time)
    (hstep : ∀ j,j<n → ∀ a,dist (site (τ j a)) (site a)≤1)
    (hmove : ∀ j,j<n → ∀ a,site (τ j a)≠site a →
      edge j∈choices (site a) ∧ site (τ j a)=next (site a) (edge j))
    (hindex : ∀ j,j<n → ∀ a,site (τ j a)≠site a → ∀ b,
      index (time j) (edge j) b=(if b then Sum.inl (r j) else Sum.inr (r j)))
    (M : (I → Bool) → I → Prop) (p : I → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    {κ δ : ℝ} (hκ : 1≤κ) (hδ : 0≤δ)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0≤W c)
    (hins : ∀ c i,W (Function.update c i true)≤κ*W (Function.update c i false))
    (hrate : ∀ t e b,
      (Sum.elim (fun _=>κ) (fun _=>(1:ℝ)) (index t e b)) * doubleRates p (index t e b)≤δ) :
    (∑ c : I ⊕ I → Bool,if (R:ℝ)≤dist (site v)
      (site (trajectory τ (mixedCoins M c r) n v)) then
      weight (doubleRates p) c*W (original c) else 0) ≤
      ((N+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R*(∑ c,weight p c*W c) := by
  let x : (I ⊕ I → Bool) → ℕ → X := fun c j=>site (trajectory τ (mixedCoins M c r) j v)
  have hd (c : I ⊕ I → Bool) (j : ℕ) (_hj : j<n) (hne : x c (j+1)≠x c j) :
      mixedCoins M c r j=true ∧
      x c (j+1)=site (τ j (trajectory τ (mixedCoins M c r) j v)) ∧
      site (τ j (trajectory τ (mixedCoins M c r) j v))≠x c j := by
    have hc : mixedCoins M c r j=true := by
      by_contra hh
      simp only [x,trajectory_succ,ite_eq_right hh] at hne
      exact hne rfl
    refine ⟨hc,?_,?_⟩
    · simp only [x,trajectory_succ,hc,ite_true]
    · simpa only [x,trajectory_succ,hc,ite_true] using hne
  have hi (c : I ⊕ I → Bool) (j : ℕ) (hj : j<n) (hne : x c (j+1)≠x c j) :
      index (time j) (edge j) (mixedSource M c r j)=
        (if mixedSource M c r j then Sum.inl (r j) else Sum.inr (r j)) :=
    hindex j hj _ (hd c j hj hne).2.2 _
  have hb (c : I ⊕ I → Bool) : Set.InjOn
      (fun j=>index (time j) (edge j) (mixedSource M c r j))
      {j | j<n ∧ x c (j+1)≠x c j} := by
    intro j hj k hk he
    dsimp only at he
    rw [hi c j hj.1 hj.2,hi c k hk.1 hk.2] at he
    apply hr hj.1 hk.1
    have he' := congrArg (Sum.elim id id) he
    split_ifs at he' <;> exact he'
  have hm (c : I ⊕ I → Bool) (j : ℕ) (hj : j<n) (hne : x c (j+1)≠x c j) :
      edge j∈choices (x c j) ∧ x c (j+1)=next (x c j) (edge j) ∧
      c (index (time j) (edge j) (mixedSource M c r j))=true := by
    have hh:=hd c j hj hne
    obtain ⟨h1,h2⟩:=hmove j hj _ hh.2.2
    refine ⟨h1,hh.2.1.trans h2,?_⟩
    rw [hi c j hj hne,←mixedCoins_index M c r j]
    exact hh.1
  have hs (c : I ⊕ I → Bool) (j : ℕ) (hj : j<n) : dist (x c j) (x c (j+1))≤1 := by
    dsimp only [x]
    rw [trajectory_succ]
    split_ifs
    · rw [dist_comm]; exact hstep j hj _
    · simp
  have hh:=adaptive_trajectory_probability choices next B hB (site v) x (fun _=>rfl)
    edge n N R time index (fun c=>mixedSource M c r) htime hb hs hm
    (doubleRates p) (Sum.elim (fun _=>κ) (fun _=>(1:ℝ)))
    (by intro i; cases i <;> exact hp _) (by intro i; cases i <;> simp [hκ])
    (fun c=>W (original c)) (fun c=>hW _)
    (by
      intro c i
      convert double_insertion W hins c i using 1 <;>
        congr 2 <;> funext j <;> simp only [original,Function.comp_apply,Function.update_apply] <;> split_ifs <;> rfl) δ hδ hrate
  have hz : (∑ c : I ⊕ I → Bool,weight (doubleRates p) c*W (original c)) =
      ∑ c : I → Bool,weight p c*W c := by
    convert double_partition p W using 1
  convert hh using 1
  · congr 1
    ext c
    simp
  · rw [←hz]
    congr 2
    ext c
    simp

end Heisenberg.Clocks

open scoped BigOperators Classical
namespace Heisenberg.Serial

section
open Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks Heisenberg.MeshPair
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I]

theorem sampledPrefix_event (τ : ℕ → Equiv.Perm V) (p : I → ℝ)
    (hp : ∀ i,0≤p i ∧ p i≤1) (r : ℕ → I) (n : ℕ)
    (hr : Set.InjOn r (Set.Iio n)) (M : (I → Bool) → I → Prop)
    (D : (I → Bool) → Fin (n+1) → Set V)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0≤W c) (v : V) (A : Set V) :
    (∑ base : I → Bool,weight p base*W base*
      (∑ i,if i∈A then sampledPrefix τ p r M n D base i v else 0)) ≤
    ∑ c : I ⊕ I → Bool,if trajectory τ (mixedCoins M c r) n v∈A then
      weight (doubleRates p) c*W (original c) else 0 := by
  have hir : Function.Injective (fun i : Fin n=>r i) := by
    intro i j h
    exact Fin.ext (hr i.isLt j.isLt h)
  have hw (i : I) : (∑ b : Bool,if b then p i else 1-p i)=1 := by simp
  have hw0 (i : I) (b : Bool) : 0≤(if b then p i else 1-p i) := by
    cases b <;> simp <;> linarith [(hp i).1,(hp i).2]
  have hbase (base : I → Bool) := prefix_endpoint_bound n
    (fun i b=>if b then p i else 1-p i) hw hw0 (fun i=>r i) hir (D base)
    (fun i b=>if (if M base (r i) then base (r i) else b) then τ i else 1) v A
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun base _=>
    mul_le_mul_of_nonneg_left (hbase base)
      (mul_nonneg (weight_nonneg p hp base) (hW base)))
  change (∑ base : I → Bool,weight p base*W base*
      (∑ i,if i∈A then sampledPrefix τ p r M n D base i v else 0)) ≤ _ at h
  apply h.trans_eq
  simp only [Finset.mul_sum]
  rw [←(Equiv.sumArrowEquivProdArrow I I Bool).symm.sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro base _
  apply Finset.sum_congr rfl
  intro c _
  have he : follow n (fun i=>if (if M base (r i) then base (r i) else c (r i)) then τ i else 1) v=
      trajectory τ (fun j=>if M base (r j) then base (r j) else c (r j)) n v :=
    follow_trajectory τ (fun j=>if M base (r j) then base (r j) else c (r j)) n v
  change weight p base*W base*(if follow n _ v∈A then productWeight _ c else 0) = _
  rw [he]
  have ho : original ((Equiv.sumArrowEquivProdArrow I I Bool).symm (base,c))=base := rfl
  have hf : fresh ((Equiv.sumArrowEquivProdArrow I I Bool).symm (base,c))=c := rfl
  have hc : mixedCoins M ((Equiv.sumArrowEquivProdArrow I I Bool).symm (base,c)) r=
      (fun j=>if M base (r j) then base (r j) else c (r j)) := by
    funext j
    simp only [mixedCoins,ho,hf]
  rw [hc,double_weight,ho,hf]
  split_ifs <;> simp only [productWeight,weight,mul_zero]
  ring

end

open Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks Heisenberg.MeshPair
variable {V X E I : Type*} [Fintype V] [DecidableEq V] [PseudoMetricSpace X] [Fintype E] [Fintype I]

theorem sampledPrefix_localization
    (choices : X → Finset E) (next : X → E → X) (B : ℕ)
    (hB : ∀ x,(choices x).card≤B)
    (τ : ℕ → Equiv.Perm V) (site : V → X) (v : V)
    (r : ℕ → I) (n N R : ℕ) (hr : Set.InjOn r (Set.Iio n))
    (edge : ℕ → E) (time : ℕ → Fin N) (index : Fin N → E → Bool → I ⊕ I)
    (htime : Monotone time)
    (hstep : ∀ j,j<n → ∀ a,dist (site (τ j a)) (site a)≤1)
    (hmove : ∀ j,j<n → ∀ a,site (τ j a)≠site a →
      edge j∈choices (site a) ∧ site (τ j a)=next (site a) (edge j))
    (hindex : ∀ j,j<n → ∀ a,site (τ j a)≠site a → ∀ b,
      index (time j) (edge j) b=(if b then Sum.inl (r j) else Sum.inr (r j)))
    (M : (I → Bool) → I → Prop) (p : I → ℝ) (hp : ∀ i,0≤p i ∧ p i≤1)
    {κ δ : ℝ} (hκ : 1≤κ) (hδ : 0≤δ)
    (W : (I → Bool) → ℝ) (hW : ∀ c,0≤W c)
    (hins : ∀ c i,W (Function.update c i true)≤κ*W (Function.update c i false))
    (D : (I → Bool) → Fin (n+1) → Set V)
    (hrate : ∀ t e b,
      (Sum.elim (fun _=>κ) (fun _=>(1:ℝ)) (index t e b)) * doubleRates p (index t e b)≤δ) :
    (∑ base : I → Bool, weight p base*W base*
      (∑ j,if (R:ℝ)<dist (site j) (site v) then sampledPrefix τ p r M n D base j v else 0)) ≤
      ((N+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R*(∑ c,weight p c*W c) := by
  have he := sampledPrefix_event τ p hp r n hr M D W hW v {j | (R:ℝ)<dist (site j) (site v)}
  have hl := joint_trajectory_localization choices next B hB τ site v r n N R hr edge time index
    htime hstep hmove hindex M p hp hκ hδ W hW hins hrate
  apply he.trans
  apply le_trans _ hl
  apply Finset.sum_le_sum
  intro c _
  change (if (R:ℝ)<dist (site (trajectory τ (mixedCoins M c r) n v)) (site v) then _ else 0)≤_
  by_cases hc : (R:ℝ)<dist (site (trajectory τ (mixedCoins M c r) n v)) (site v)
  · have hc' : (R:ℝ)≤dist (site v) (site (trajectory τ (mixedCoins M c r) n v)) := by
      rw [dist_comm]; exact hc.le
    rw [ite_eq_left hc,ite_eq_left hc']
  · rw [ite_eq_right hc]
    split_ifs
    · exact mul_nonneg (weight_nonneg (doubleRates p) (by intro i; cases i <;> exact hp _) c) (hW _)
    · rfl

end Heisenberg.Serial

open scoped Classical

open scoped Classical BigOperators

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_CutContractions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical RealInnerProductSpace
namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.LatticeRegular Heisenberg.RoutedFlow Heisenberg.SpatialFrame
open Heisenberg.MeshPair Heisenberg.Exposure
variable {k : ℕ}

theorem exposed_prefix_leakage (hk : 2≤k) (L : ℝ) (hL : 0≤L) :
    ∃ M : ℕ,∃ C≥0,∀ (T B : Type) [Fintype T] [Fintype B] [Nonempty B]
      (Λ F : Finset (ZSite k)) (s : Equiv.Perm T)
      (a b : T → Slots (B:=B) Λ) (p : T → ℝ)
      (_hp : ∀ i,0≤p i ∧ p i≤1) (pins : Set (T×Slots (B:=B) Λ))
      (r : ℕ → T) (c : ℕ → ℕ) (J : Finset (Slots (B:=B) Λ))
      (f : (T → Bool) → EuclideanSpace ℝ (Slots (B:=B) Λ))
      (a₀ b₀ : ℕ → Slots (B:=B) Λ) (q n R : ℕ) (e : Fin q ≃ Edges Step Λ)
      (δ ρ ζ rem : ℝ),
      0<n → 0<δ → 0≤rem → (∀ j,r (j+1)=s (r j)) →
      (∀ i : Fin q,a₀ i=(e i).val.1) → (∀ i : Fin q,b₀ i=(e i).val.2) →
      F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
      (∀ base j,j∈J → j∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base pins (r 0) ∧ j.1.val∈F) →
      (∀ base j,j∈J → (f base).ofLp j=1) →
      (∀ base j,0≤(f base).ofLp j ∧ (f base).ofLp j≤1) →
      (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base pins (r 0)∩{j | j.1.val∈F} →
        (f base).ofLp j=0) →
      (∀ z u,0≤u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z≤u)).card:ℝ)≤
        L*(1+u)^((1:ℝ)/100)) →
      (∀ (i : Fin n) (j : J), (∑ base, Exposure.layerMass s a b pins p base *
        (if ¬Regular (blocked Λ (holeCut s (fun l=>Equiv.swap (a l) (b l)) base pins (r (c i))))
          j.val.1.val R M (1/(100*(k+1:ℝ))) then (1:ℝ) else 0))≤ρ) →
      (∀ (i : Fin n) (j : J), (∑ base,Exposure.layerMass s a b pins p base *
        (∑ v,if (R:ℝ)<dist v.1.val j.val.1.val then
          prefixMatrix (fun l=>exposedStep s a b base pins {v | v.1.val∈F} p (r l)) (c i) v j.val else 0))≤ζ) →
      (∀ i : Fin n,2*δ*(∑ base,Exposure.layerMass s a b pins p base *
        MeshPair.quietEnergy (holeCut s (fun l=>Equiv.swap (a l) (b l)) base pins (r (c i)))
          a₀ b₀ q (exposedSweep s a b base pins {v | v.1.val∈F} p r (c i) (f base)))≤
        (∑ base,Exposure.layerMass s a b pins p base *
          (‖exposedSweep s a b base pins {v | v.1.val∈F} p r (c i) (f base)‖^2-
            ‖exposedSweep s a b base pins {v | v.1.val∈F} p r (c (i+1)) (f base)‖^2))+rem) →
      (J.card:ℝ)-2*((ρ+ζ)*J.card)-
        2*(C*(1+(R:ℝ))^((1:ℝ)/100)*J.card)/(δ*(n:ℝ))-(n:ℝ)*rem ≤
      ∑ base,Exposure.layerMass s a b pins p base *
        (‖f base‖^2-‖exposedSweep s a b base pins {v | v.1.val∈F} p r (c n) (f base)‖^2) := by
  obtain ⟨M,C,hC,hh⟩ := routed_mean_leakage hk L hL
  refine ⟨M,C,hC,?_⟩
  intro T B _ _ _ Λ F s a b p hp pins r c J f a₀ b₀ q n R e δ ρ ζ rem hn hδ hrem
    hr ha hb hF hframe hJ hfJ hf hs hg hbad hesc hloss
  let I : Set (Slots (B:=B) Λ) := {v | v.1.val∈F}
  let H : (T → Bool) → ℕ → Set (Slots (B:=B) Λ) :=
    fun base i=>holeCut s (fun l=>Equiv.swap (a l) (b l)) base pins (r (c i))
  let A : (T → Bool) → ℕ → Matrix (Slots (B:=B) Λ) (Slots (B:=B) Λ) ℝ :=
    fun base i=>prefixMatrix (fun l=>exposedStep s a b base pins I p (r l)) (c i)
  let P := fun base i=>euclideanMap (A base i)
  let K := fun base i v (j : J)=>A base i v j.val
  let eta := indicatorVector J
  let g := fun base=>f base-eta
  have heq (base : T → Bool) : eta+g base=f base := by simp [g]
  have hA (base : T → Bool) (i : ℕ) : MatrixContraction.DoublySubstochastic (A base i) :=
    prefix_substochastic _ _ (fun l _=>exposedStep_substochastic s a b base pins I p hp (r l))
  have hPf (base : T → Bool) (i : ℕ) : P base i (eta+g base)=
      exposedSweep s a b base pins I p r (c i) (f base) := by
    rw [heq,exposedSweep_prefix]
  have hsupp (base : T → Bool) (i : ℕ) := exposedSweep_supported s a b base pins I p r (c i)
    (fun j _=>hr j) (f base) (hs base)
  have hnorm (base : T → Bool) (i : ℕ) (v : EuclideanSpace ℝ (Slots (B:=B) Λ)) :
      ‖P base i v‖≤‖v‖ := by
    change ‖euclideanMap (A base i) v‖≤‖v‖
    exact euclideanMap_contraction _ (hA base i) v
  have h := hh (T → Bool) J B Λ F H (fun j : J=>j.val.1.val) R
    (Exposure.layerMass s a b pins p) eta g P K a₀ b₀ q n e δ ρ ζ rem hn hδ hrem ha hb hF hframe
    (layerMass_nonneg s a b pins p hp) (layerMass_sum s a b pins p hp)
    (fun base=>indicatorVector_orth J (f base) (hfJ base))
    (fun base i _=>hnorm base i)
    (by
      intro base i j hj
      rw [hPf]
      exact hsupp base i j (fun h=>hj h.2))
    (by
      intro base i
      rw [hPf]
      exact exposedSweep_bounds s a b base pins I p hp r (c i) (f base) (hf base))
    (fun base i v j=>(hA base i).nonneg v j.val)
    (fun base i j=>(hA base i).col j.val) hg
    (by
      intro base i v j hv
      by_contra hnot
      apply hv
      exact exposedPrefix_column_support s a b base pins I p r (c i)
        (fun l _=>hr l) j.val (by simpa only [I,Set.mem_inter_iff,Set.mem_ofPred_eq] using hJ base j.val j.property) v (fun h=>hnot h.1))
    (fun base i=>indicatorVector_pairing (A base i) J (P base i (eta+g base)))
    hbad hesc (by intro i; simpa only [hPf, H, I, Exposure.quietEnergy, MeshPair.quietEnergy] using hloss i)
  have hPf' (base : T → Bool) (i : ℕ) : P base i (f base)=
      exposedSweep s a b base pins I p r (c i) (f base) := by
    simpa only [heq] using hPf base i
  simpa only [eta,indicatorVector_sq,Fintype.card_coe,heq,hPf',I] using h

end Heisenberg.Flow

end

noncomputable section
open scoped Classical Fin.NatCast
namespace Heisenberg.Schedule
variable {m Q : ℕ} [NeZero m]

lemma run_succ (t : Fin m) (j : ℕ) : run t (j+1)=finRotate m (run t j) := by
  simp [run,Nat.cast_add,add_assoc]
lemma run_val (t : Fin m) (j : ℕ) : (run t j).val=(t.val+j)%m := by
  simp [run,Fin.val_add,Nat.add_mod]
lemma run_inj (t : Fin m) {n : ℕ} (hn : n ≤ m) : Set.InjOn (run t) (Set.Iio n) := by
  intro i hi j hj h
  have he : (↑i:Fin m)=(↑j:Fin m) := add_left_cancel h
  have hh := congrArg Fin.val he
  simpa only [Fin.val_natCast,Nat.mod_eq_of_lt (lt_of_lt_of_le hi hn),
    Nat.mod_eq_of_lt (lt_of_lt_of_le hj hn)] using hh

omit [NeZero m] in
lemma warm_le (t : Fin m) : warm t Q≤Q := Nat.sub_le ..
omit [NeZero m] in
lemma cut_step (t : Fin m) (i : ℕ) : cut t Q (i+1)=cut t Q i+Q := by
  simp [cut,Nat.add_mul,Nat.add_assoc]
lemma cut_mod (t : Fin m) (hQ : 0<Q) (hdiv : Q∣m) (i j : ℕ) :
    (run t (cut t Q i+j)).val%Q=j%Q := by
  rw [run_val,Nat.mod_mod_of_dvd _ hdiv]
  have h := Nat.mod_lt t.val hQ
  have hw : (t.val+warm t Q)%Q=0 := by
    have he : t.val%Q+(Q-t.val%Q)=Q := Nat.add_sub_of_le h.le
    change (t.val+(Q-t.val%Q))%Q=0
    calc
      _ = (t.val%Q+(Q-t.val%Q))%Q := by simp [Nat.add_mod]
      _ = 0 := by rw [he,Nat.mod_self]
  have he : t.val+(cut t Q i+j)=(t.val+warm t Q)+i*Q+j := by simp [cut,Nat.add_assoc]
  rw [he]
  simp only [Nat.add_mod,hw,Nat.mul_mod_left,Nat.zero_mod,Nat.zero_add,Nat.mod_mod]

omit [NeZero m] in
lemma round_mono (t : Fin m) : Monotone (round t Q) := by
  intro i j hij
  exact Nat.div_le_div_right (Nat.add_le_add_left hij _)
omit [NeZero m] in
lemma round_lt (t : Fin m) (hQ : 0<Q) {j u : ℕ} (hj : j≤u*Q) : round t Q j<u+1 := by
  apply (Nat.div_lt_iff_lt_mul hQ).mpr
  have h := Nat.mod_lt t.val hQ
  nlinarith

lemma clock_mod (t : Fin m) (hdiv : Q∣m) (g l : ℕ) :
    (clock t Q g l).val%Q=l%Q := by
  simp only [clock,Nat.mod_mod_of_dvd _ hdiv,Nat.add_mod,Nat.mul_mod_left,
    Nat.zero_add,Nat.mod_mod]
lemma clock_run (t : Fin m) (j : ℕ) :
    clock t Q (round t Q j) ((t.val+j)%Q)=run t j := by
  apply Fin.ext
  rw [run_val]
  change (((t.val/Q+(t.val%Q+j)/Q)*Q+(t.val+j)%Q)%m)=(t.val+j)%m
  congr 1
  have h₁ := Nat.mod_add_div t.val Q
  have h₂ := Nat.mod_add_div (t.val%Q+j) Q
  have h₃ : (t.val+j)%Q=(t.val%Q+j)%Q := by simp [Nat.add_mod]
  rw [h₃]
  nlinarith
lemma clock_run_phase (t : Fin m) (hdiv : Q∣m) (j : ℕ) :
    clock t Q (round t Q j) ((run t j).val%Q)=run t j := by
  rw [run_val,Nat.mod_mod_of_dvd _ hdiv]
  exact clock_run t j

end Heisenberg.Schedule
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ScheduledResiduals
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Classical Fin.NatCast

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.Serial
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Bernoulli Heisenberg.Clocks
variable {V T X E : Type} [Fintype V] [DecidableEq V] [Fintype T]
  [PseudoMetricSpace X] [Fintype E]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma product_snoc (n : ℕ) (K : Fin (n+1) → Matrix V V ℝ) :
    product (n+1) K=K (Fin.last n)*product n (fun i=>K i.castSucc) := by
  induction n with
  | zero => simp [product]
  | succ n ih =>
    rw [product,ih,product,Matrix.mul_assoc]
    rfl

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma prefix_product (K : ℕ → Matrix V V ℝ) (n : ℕ) :
    prefixMatrix K n=product n (fun i=>K i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [prefixMatrix,product_snoc]
    simpa only [Fin.val_last,Fin.val_castSucc] using congrArg (K n * ·) ih

omit [Fintype V] [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma residualBetween_coin (D F : Set V) (M : Prop) (base : Bool) (a b : V) (p : ℝ) :
    (∑ z : Bool,(if z then p else 1-p) •
      killedBetween D F (if (if M then base else z) then Equiv.swap a b else 1))=
      residualBetween D F M base a b p := by
  by_cases hM : M
  · simp only [hM,ite_true,residualBetween]
    rw [←Finset.sum_smul]
    simp
  · simp [hM,residualBetween,add_comm]

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma mul_projection_column (A : Matrix V V ℝ) (D : Set V) {j : V} (hj : j∈D) (v : V) :
    (A*projection D) v j=A v j := by
  simp only [Matrix.mul_apply,projection,killedBetween,Equiv.Perm.one_apply]
  rw [Finset.sum_eq_single j]
  · simp [hj]
  · intro k _ hk
    simp [hk]
  · simp

omit [Fintype T] [PseudoMetricSpace X] [Fintype E] in
lemma sampledPrefix_exposed (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V))
    (I : Set V) (p : T → ℝ) (r : ℕ → T) (n : ℕ)
    (hr : ∀ j,j<n → r (j+1)=s (r j)) (base : T → Bool) :
    sampledPrefix (fun j=>Equiv.swap (a (r j)) (b (r j))) p r
      (fun base=>layerRevealed (fun i=>Equiv.swap (a i) (b i))
        (Heisenberg.Cycle.MissingSet (layerHistory s (fun i=>Equiv.swap (a i) (b i)) base) P)) n
      (fun base j=>holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r j)∩I) base=
    prefixMatrix (fun j=>exposedStep s a b base P I p (r j)) n *
      projection (holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) := by
  rw [sampledPrefix,prefix_product]
  congr 1
  congr 1
  funext j
  rw [residualBetween_coin]
  simp only [exposedStep,Fin.val_castSucc,Fin.val_succ,hr j j.isLt]

theorem exposedPrefix_localization
    (choices : X → Finset E) (next : X → E → X) (B : ℕ) (hB : ∀ x,(choices x).card≤B)
    (loc : V → X) (s : Equiv.Perm T) (a b : T → V) (P : Set (T×V))
    (I : Set V) (p : T → ℝ) (hp : ∀ j,0≤p j ∧ p j≤1)
    (r : ℕ → T) (n N R : ℕ) (hr : ∀ j,j<n → r (j+1)=s (r j))
    (hir : Set.InjOn r (Set.Iio n))
    (edge : ℕ → E) (time : ℕ → Fin N) (index : Fin N → E → Bool → T⊕T)
    (htime : Monotone time)
    (hstep : ∀ j,j<n → ∀ v,dist (loc (Equiv.swap (a (r j)) (b (r j)) v)) (loc v)≤1)
    (hmove : ∀ j,j<n → ∀ v,loc (Equiv.swap (a (r j)) (b (r j)) v)≠loc v →
      edge j∈choices (loc v) ∧ loc (Equiv.swap (a (r j)) (b (r j)) v)=next (loc v) (edge j))
    (hindex : ∀ j,j<n → ∀ v,loc (Equiv.swap (a (r j)) (b (r j)) v)≠loc v → ∀ c,
      index (time j) (edge j) c=(if c then Sum.inl (r j) else Sum.inr (r j)))
    {δ : ℝ} (hδ : 0≤δ)
    (hrate : ∀ t e c,(Sum.elim (fun _=>(2:ℝ)) (fun _=>(1:ℝ)) (index t e c))*
      doubleRates p (index t e c)≤δ)
    (v : V) (hv : ∀ base,v∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (r 0)∩I) :
    (∑ base,layerMass s a b P p base *
      (∑ j,if (R:ℝ)<dist (loc j) (loc v) then
        prefixMatrix (fun l=>exposedStep s a b base P I p (r l)) n j v else 0)) ≤
      ((N+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R := by
  let τ := fun j=>Equiv.swap (a j) (b j)
  let M := fun base=>layerRevealed τ (Heisenberg.Cycle.MissingSet (layerHistory s τ base) P)
  let D := fun base (j : Fin (n+1))=>holeCut s τ base P (r j)∩I
  have h := sampledPrefix_localization choices next B hB (fun j=>τ (r j)) loc v r n N R hir
    edge time index htime hstep hmove hindex M p hp (κ:=2) (by norm_num) hδ
    (layerWeight s a b P) (layerWeight_nonneg s a b P) (layerWeight_insertion s a b P)
    D hrate
  have he (base : T → Bool) (j : V) :
      sampledPrefix (fun j=>τ (r j)) p r M n D base j v=
        prefixMatrix (fun l=>exposedStep s a b base P I p (r l)) n j v := by
    rw [sampledPrefix_exposed s a b P I p r n hr base]
    exact mul_projection_column _ _ (hv base) j
  simp only [he] at h
  have hz : 0<layerPartition s a b P p := lt_of_lt_of_le zero_lt_one (layerPartition_one_le s a b P p hp)
  simp only [layerMass,div_mul_eq_mul_div,←Finset.sum_div]
  apply (div_le_iff₀ hz).mpr
  exact h

end Heisenberg.Serial

end
end

noncomputable section
open scoped BigOperators Classical
namespace Heisenberg.SpatialFrame
open Heisenberg.Geometry
variable {d : ℕ} {B : Type} [Fintype B]

lemma step_mem_neighbors {x y : Site d} (h : Step x y) : y∈neighbors x := by
  obtain ⟨j,h,hj⟩:=h
  rcases h with h|h
  · refine Finset.mem_image.mpr ⟨(j,true),Finset.mem_univ _,?_⟩
    funext k
    by_cases hk : k=j
    · subst k; simp [h]
    · simp [hk,←hj k hk]
  · refine Finset.mem_image.mpr ⟨(j,false),Finset.mem_univ _,?_⟩
    funext k
    by_cases hk : k=j
    · subst k; simp; omega
    · simp [hk,←hj k hk]

lemma neighbors_card (x : Site d) : (neighbors x).card≤2*d := by
  exact (Finset.card_image_le).trans (by simp [mul_comm])

lemma choices_card (Λ : Finset (Site d)) (x : Site d) :
    (choices (B:=B) Λ x).card≤4*d*(Fintype.card B)^2 := by
  let C := ((neighbors x).image (fun y=>(x,y)))∪((neighbors x).image (fun y=>(y,x)))
  let code : Edges (B:=B) Step Λ → (Site d × Site d) × (B×B) :=
    fun e=>((e.val.1.1.val,e.val.2.1.val),(e.val.1.2,e.val.2.2))
  have hm : Set.MapsTo code (↑(choices (B:=B) Λ x) : Set (Edges (B:=B) Step Λ)) (↑(C ×ˢ (Finset.univ : Finset (B×B))) : Set ((Site d × Site d) × (B×B))) := by
    intro e he
    apply Finset.mem_product.mpr
    refine ⟨?_,Finset.mem_univ _⟩
    rcases (Finset.mem_filter.mp he).2 with h|h
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨e.val.2.1.val,?_,?_⟩
      · exact step_mem_neighbors (h ▸ e.property)
      · exact Prod.ext h.symm rfl
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨e.val.1.1.val,?_,?_⟩
      · exact step_mem_neighbors (h ▸ step_symm e.property)
      · exact Prod.ext rfl h.symm
  have hi : Function.Injective code := by
    intro e f h
    apply Subtype.ext
    apply Prod.ext
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun z : (Site d × Site d) × (B×B)=>z.1.1) h)
      · exact congrArg (fun z : (Site d × Site d) × (B×B)=>z.2.1) h
    · apply Prod.ext
      · exact Subtype.ext (congrArg (fun z : (Site d × Site d) × (B×B)=>z.1.2) h)
      · exact congrArg (fun z : (Site d × Site d) × (B×B)=>z.2.2) h
  have hC : C.card≤4*d := by
    exact (Finset.card_union_le _ _).trans ((add_le_add
      (Finset.card_image_le.trans (neighbors_card x))
      (Finset.card_image_le.trans (neighbors_card x))).trans (by omega))
  calc
    _ ≤ (C ×ˢ (Finset.univ : Finset (B×B))).card := Finset.card_le_card_of_injOn code hm hi.injOn
    _ = C.card*(Fintype.card B)^2 := by simp [pow_two]
    _ ≤ _ := Nat.mul_le_mul_right _ hC

omit [Fintype B] in
lemma edge_site_ne {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) :
    e.val.1.1.val≠e.val.2.1.val := by
  intro h
  obtain ⟨j,hj,_⟩:=e.property
  rw [h] at hj
  omega

omit [Fintype B] in
lemma swap_step {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) (v : Slots (B:=B) Λ) :
    dist (Equiv.swap e.val.1 e.val.2 v).1.val v.1.val≤1 := by
  by_cases h₁ : v=e.val.1
  · subst v
    rw [Equiv.swap_apply_left,dist_comm]
    exact step_dist_le_one e.property
  by_cases h₂ : v=e.val.2
  · subst v
    rw [Equiv.swap_apply_right]
    exact step_dist_le_one e.property
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  simp

lemma swap_move {Λ : Finset (Site d)} (e : Edges (B:=B) Step Λ) (v : Slots (B:=B) Λ)
    (h : (Equiv.swap e.val.1 e.val.2 v).1.val≠v.1.val) :
    e∈choices Λ v.1.val ∧ (Equiv.swap e.val.1 e.val.2 v).1.val=next v.1.val e := by
  by_cases h₁ : v=e.val.1
  · subst v; simp [choices,next]
  by_cases h₂ : v=e.val.2
  · subst v; simp [choices,next,(edge_site_ne e).symm]
  rw [Equiv.swap_apply_of_ne_of_ne h₁ h₂] at h
  exact False.elim (h rfl)

end Heisenberg.SpatialFrame
end
end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_ReversedExposure
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped BigOperators Classical Fin.NatCast
namespace Heisenberg.Schedule
open Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.Serial Heisenberg.Clocks
variable {T V X : Type} [Fintype T] [Fintype V] [DecidableEq V] [PseudoMetricSpace X]

theorem indexed_cyclic_localization {m q Q : ℕ} [NeZero m] [NeZero q]
    (s : Equiv.Perm T) (e : Fin m ≃ T) (he : ∀ j,s (e j)=e (finRotate m j))
    (hQ : 0<Q) (hqQ : q≤Q) (hdiv : Q∣m)
    (loc : V → X) (choices : X → Finset (Fin q)) (next : X → Fin q → X)
    (B : ℕ) (hB : ∀ x,(choices x).card≤B)
    (a₀ b₀ : Fin q → V) (a b : T → V)
    (hab : ∀ j : Fin m,∀ hj : j.val%Q<q,a (e j)=a₀ ⟨j.val%Q,hj⟩ ∧ b (e j)=b₀ ⟨j.val%Q,hj⟩)
    (hsite : ∀ j : Fin m,q≤j.val%Q → loc (a (e j))=loc (b (e j)))
    (hstep : ∀ e v,dist (loc (Equiv.swap (a₀ e) (b₀ e) v)) (loc v)≤1)
    (hmove : ∀ e v,loc (Equiv.swap (a₀ e) (b₀ e) v)≠loc v →
      e∈choices (loc v) ∧ loc (Equiv.swap (a₀ e) (b₀ e) v)=next (loc v) e)
    (P : Set (T×V)) (I : Set V) (p : T → ℝ)
    (hp : ∀ j,0≤p j ∧ p j≤1) (δ : ℝ) (hδ : 0≤δ)
    (hrate : ∀ j : Fin m,j.val%Q<q → 2*p (e j)≤δ)
    (t : Fin m) (n u R : ℕ) (hn : n ≤ m) (hu : n ≤ u * Q)
    (v : V) (hv : ∀ base,v∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (e t)∩I) :
    (∑ base,layerMass s a b P p base *
      (∑ j,if (R:ℝ)<dist (loc j) (loc v) then
        prefixMatrix (fun l=>exposedStep s a b base P I p (e (run t l))) n j v else 0)) ≤
      ((u+1+R).choose R:ℝ)*(2*(B:ℝ)*δ)^R := by
  let edge : ℕ → Fin q := fun j=>⟨(run t j).val%Q%q,Nat.mod_lt _ (NeZero.pos q)⟩
  let time : ℕ → Fin (u+1) := fun j=>⟨min (round t Q j) u,by omega⟩
  let index : Fin (u+1) → Fin q → Bool → T⊕T := fun g edge c=>
    if c then Sum.inl (e (clock t Q g edge)) else Sum.inr (e (clock t Q g edge))
  have htime : Monotone time := by
    intro i j hij
    exact min_le_min_right u (round_mono t hij)
  have hother (j : Fin m) (hj : q≤j.val%Q) (v : V) :
      loc (Equiv.swap (a (e j)) (b (e j)) v)=loc v := by
    by_cases ha : v=a (e j)
    · subst v; simpa using (hsite j hj).symm
    by_cases hb : v=b (e j)
    · subst v; simpa using hsite j hj
    rw [Equiv.swap_apply_of_ne_of_ne ha hb]
  have hsp (j : ℕ) (hj : (run t j).val%Q<q) :
      a (e (run t j))=a₀ (edge j) ∧ b (e (run t j))=b₀ (edge j) := by
    simpa only [edge,Nat.mod_eq_of_lt hj] using hab (run t j) hj
  have hir : Set.InjOn (fun j=>e (run t j)) (Set.Iio n) := by
    intro i hi j hj h
    exact run_inj t hn hi hj (e.injective h)
  apply exposedPrefix_localization choices next B hB loc s a b P I p hp
    (fun j=>e (run t j)) n (u+1) R
    (fun j _=>by rw [run_succ,←he]) hir edge time index htime
  · intro j _ w
    by_cases hj : (run t j).val%Q<q
    · rw [(hsp j hj).1,(hsp j hj).2]
      exact hstep _ w
    · rw [hother _ (Nat.le_of_not_gt hj) w]
      simp
  · intro j _ w hw
    have hj : (run t j).val%Q<q := by
      by_contra h
      exact hw (hother _ (Nat.le_of_not_gt h) w)
    rw [(hsp j hj).1,(hsp j hj).2] at hw ⊢
    exact hmove _ w hw
  · intro j hj w hw c
    have hphase : (run t j).val%Q<q := by
      by_contra h
      exact hw (hother _ (Nat.le_of_not_gt h) w)
    have ht : (time j).val=round t Q j := by
      exact min_eq_left (Nat.le_of_lt_succ (round_lt t hQ (le_trans (Nat.le_of_lt hj) hu)))
    have he : (edge j).val=(run t j).val%Q := Nat.mod_eq_of_lt hphase
    simp only [index,ht,he,clock_run_phase t hdiv]
  · exact hδ
  · intro g edge c
    have hc : (clock t Q g edge).val%Q<q := by
      rw [clock_mod t hdiv,Nat.mod_eq_of_lt (lt_of_lt_of_le edge.isLt hqQ)]
      exact edge.isLt
    have hh := hrate (clock t Q g edge) hc
    cases c <;> simp only [index,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inr,Sum.elim_inl,Heisenberg.Bernoulli.doubleRates,one_mul]
    · linarith [(hp (e (clock t Q g edge))).1]
    · exact hh
  · simpa only [run_zero] using hv

end Heisenberg.Schedule

end

end

end OAI
end

section
-- module Solutions.OAIW2_Heis.Heisenberg_PeriodicLeakage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
lemma swap_classical {α : Type*} [h : DecidableEq α] (a b : α) :
    Equiv.swap a b = @Equiv.swap α (Classical.decEq α) a b := by
  have he : h=Classical.decEq α := Subsingleton.elim _ _
  cases he
  rfl
lemma exposedSweep_classical {T V : Type*} [fv : Fintype V]
    [h : DecidableEq V] :
    @Heisenberg.Exposure.exposedSweep T V fv h =
      @Heisenberg.Exposure.exposedSweep T V fv (Classical.decEq V) := by
  have he : h=Classical.decEq V := Subsingleton.elim _ _
  cases he
  rfl

end

noncomputable section
open scoped Classical BigOperators Fin.NatCast
namespace Heisenberg.SpatialFrame
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.MeshPair Heisenberg.Exposure
variable {d : ℕ} {B T : Type} [Fintype B] [Fintype T]

theorem frame_indexed_localization {m q Q : ℕ} [NeZero m] [NeZero q]
    (s : Equiv.Perm T) (ι : Fin m ≃ T) (hι : ∀ j,s (ι j)=ι (finRotate m j))
    (hQ : 0 < Q) (hqQ : q ≤ Q) (hdiv : Q∣m) (Λ : Finset (Site d))
    (e : Fin q ≃ Edges (B:=B) Step Λ) (a₀ b₀ : Fin q → Slots (B:=B) Λ)
    (ha₀ : ∀ j,a₀ j=(e j).val.1) (hb₀ : ∀ j,b₀ j=(e j).val.2)
    (a b : T → Slots (B:=B) Λ)
    (hab : ∀ j : Fin m,∀ hj : j.val%Q < q,a (ι j)=a₀ ⟨j.val%Q,hj⟩ ∧ b (ι j)=b₀ ⟨j.val%Q,hj⟩)
    (hsite : ∀ j : Fin m,q ≤ j.val%Q → (a (ι j)).1.val=(b (ι j)).1.val)
    (P : Set (T×Slots (B:=B) Λ)) (I : Set (Slots (B:=B) Λ)) (p : T → ℝ)
    (hp : ∀ j,0 ≤ p j ∧ p j ≤ 1) (δ : ℝ) (hδ : 0 ≤ δ)
    (hrate : ∀ j : Fin m,j.val%Q < q → 2*p (ι j) ≤ δ)
    (t : Fin m) (n u R : ℕ) (hn : n ≤ m) (hu : n ≤ u * Q)
    (v : Slots (B:=B) Λ)
    (hv : ∀ base,v∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t)∩I) :
    (∑ base,layerMass s a b P p base *
      (∑ j,if (R:ℝ) < dist j.1.val v.1.val then
        prefixMatrix (fun l=>exposedStep s a b base P I p (ι (run t l))) n j v else 0)) ≤
      ((u+1+R).choose R:ℝ)*(2*(4*d*(Fintype.card B)^2:ℕ)*δ)^R := by
  let C : Site d → Finset (Fin q) := fun x=>(choices (B:=B) Λ x).map e.symm.toEmbedding
  have hC : ∀ x,(C x).card ≤ 4*d*(Fintype.card B)^2 := by
    intro x
    simpa only [C,Finset.card_map] using choices_card (B:=B) Λ x
  apply indexed_cyclic_localization s ι hι hQ hqQ hdiv (fun v : Slots (B:=B) Λ=>v.1.val) C
    (fun x j=>next x (e j)) _ hC a₀ b₀ a b hab hsite
    (fun j v=>by rw [ha₀,hb₀]; exact swap_step _ _) ?_ P I p hp δ hδ hrate t n u R hn hu v hv
  intro j v h
  rw [ha₀,hb₀] at h ⊢
  obtain ⟨hc,he⟩:=swap_move (e j) v h
  refine ⟨?_,he⟩
  exact Finset.mem_map.mpr ⟨e j,hc,e.symm_apply_apply j⟩

end Heisenberg.SpatialFrame

noncomputable section
open scoped Classical BigOperators Fin.NatCast RealInnerProductSpace
open Filter Topology
namespace Heisenberg.Flow
open Heisenberg.Geometry Heisenberg.Schedule Heisenberg.SpatialFrame Heisenberg.MeshPair Heisenberg.Exposure Heisenberg.LatticeRegular
variable {d : ℕ}

attribute [local instance] OAI.Heisenberg.Flow.periodicDecEq
theorem indexed_prefix_leakage_oai (hd : 2 ≤ d) (L : ℝ) (hL : 0 ≤ L) :
    ∃ M : ℕ,∃ C ≥ 0,∀ (B : Type) [Fintype B] [Nonempty B]
      (Λ F : Finset (Site (d+1))) (q : ℕ) [NeZero q]
      (edge : Fin q ≃ Edges (B:=B) Step Λ)
      (a₀ b₀ : ℕ → Slots (B:=B) Λ)
      (_ha₀ : ∀ j : Fin q,a₀ j=(edge j).val.1)
      (_hb₀ : ∀ j : Fin q,b₀ j=(edge j).val.2)
      (ε : ℝ),0 < ε →
      ∀ᶠ δ in 𝓝 (0:ℝ),0 < δ → δ ≤ 2 →
      ∀ (T : Type) [Fintype T] (m Q : ℕ) [NeZero m]
        (s : Equiv.Perm T) (ι : Fin m ≃ T)
        (_hι : ∀ j,s (ι j)=ι (finRotate m j))
        (_hQ : 0 < Q) (_hqQ : q ≤ Q) (_hdiv : Q∣m)
        (a b : T → Slots (B:=B) Λ)
        (_hab : ∀ j : Fin m,∀ _hj : j.val%Q < q,
          a (ι j)=a₀ (j.val%Q) ∧ b (ι j)=b₀ (j.val%Q))
        (_hsite : ∀ j : Fin m,q ≤ j.val%Q → (a (ι j)).1.val=(b (ι j)).1.val)
        (p : T → ℝ) (_hp : ∀ i,0 ≤ p i ∧ p i ≤ 1)
        (_hrate : ∀ j : Fin m,j.val%Q < q → p (ι j)=δ/2)
        (P : Set (T×Slots (B:=B) Λ)) (t : Fin m)
        (J : Finset (Slots (B:=B) Λ))
        (f : (T → Bool) → EuclideanSpace ℝ (Slots (B:=B) Λ))
        (n R : ℕ) (ρ : ℝ),
        0 < n → Heisenberg.Schedule.cut t Q n ≤ m →
        F⊆Λ → (∀ z∈F,∀ w,Step z w → w∈Λ) →
        (∀ base j,j∈J → j∈holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t) ∧ j.1.val∈F) →
        (∀ base j,j∈J → (f base).ofLp j=1) →
        (∀ base j,0 ≤ (f base).ofLp j ∧ (f base).ofLp j ≤ 1) →
        (∀ base j,j∉holeCut s (fun i=>Equiv.swap (a i) (b i)) base P (ι t)∩{j | j.1.val∈F} → (f base).ofLp j=0) →
        (∀ z u,0 ≤ u → ((Finset.univ.filter (fun j : J=>dist j.val.1.val z ≤ u)).card:ℝ) ≤ L*(1+u)^((1:ℝ)/100)) →
        (∀ (i : Fin n) (j : J), (∑ base,Exposure.layerMass s a b P p base *
          (if ¬Regular (blocked Λ (holeCut s (fun l=>Equiv.swap (a l) (b l)) base P (ι (run t (Heisenberg.Schedule.cut t Q i)))))
            j.val.1.val R M (1/(100*(d+1:ℝ))) then (1:ℝ) else 0)) ≤ ρ) →
        (J.card:ℝ)-2*((ρ+((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R)*J.card)-
          2*(C*(1+(R:ℝ))^((1:ℝ)/100)*J.card)/((δ/2)*(n:ℝ))-
          (n:ℝ)*(ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) ≤
        ∑ base,Exposure.layerMass s a b P p base *
          (‖f base‖^2-‖exposedSweep s a b base P {v | v.1.val∈F} p (fun l=>ι (run t l)) (Heisenberg.Schedule.cut t Q n) (f base)‖^2) := by
  obtain ⟨M,C,hC,hflow⟩:=exposed_prefix_leakage hd L hL
  refine ⟨M,C,hC,?_⟩
  intro B _ _ Λ F q _ edge a₀ b₀ ha₀ hb₀ ε hε
  have hab₀ : ∀ j,j < q → a₀ j≠b₀ j := by
    intro j hj he
    apply edge_site_ne (edge ⟨j,hj⟩)
    have he' : (edge ⟨j,hj⟩).val.1=(edge ⟨j,hj⟩).val.2 :=
      (ha₀ ⟨j,hj⟩).symm.trans (he.trans (hb₀ ⟨j,hj⟩))
    exact congrArg (fun z : Slots (B:=B) Λ=>z.1.val) he'
  filter_upwards [round_energy a₀ b₀ q hab₀ hε] with δ hδE
  intro hδ hδ2 T _ m Q _ s ι hι hQ hqQ hdiv a b hab hsite p hp hrate P t J f n R ρ hn hhor hF hframe hJ hfJ hf hs hg hbad
  let r : ℕ → T := fun l=>ι (run t l)
  let c : ℕ → ℕ := Heisenberg.Schedule.cut t Q
  have hr : ∀ j,r (j+1)=s (r j) := by intro j; simp only [r,run_succ,←hι]
  have hc (i : ℕ) : c i+q ≤ c (i+1) := by
    dsimp only [c]
    rw [cut_step]
    omega
  have hmod (i j : ℕ) (hj : j < q) : (run t (c i+j)).val%Q=j := by
    rw [cut_mod t hQ hdiv,Nat.mod_eq_of_lt (lt_of_lt_of_le hj hqQ)]
  have ha : ∀ i j,j < q → a (r (c i+j))=a₀ j := by
    intro i j hj
    have h:= hab (run t (c i+j)) (by rw [hmod i j hj]; exact hj)
    simpa only [hmod i j hj] using h.1
  have hb : ∀ i j,j < q → b (r (c i+j))=b₀ j := by
    intro i j hj
    have h:= hab (run t (c i+j)) (by rw [hmod i j hj]; exact hj)
    simpa only [hmod i j hj] using h.2
  have hrate' : ∀ i j,j < q → p (r (c i+j))=δ/2 := by
    intro i j hj
    exact hrate _ (by rw [hmod i j hj]; exact hj)
  have hrem : 0 ≤ ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2 := by positivity
  apply hflow T B Λ F s a b p hp P r c J f a₀ b₀ q n R edge (δ/2) ρ
    (((n+2+R).choose R:ℝ)*(2*(4*(d+1)*(Fintype.card B)^2:ℕ)*δ)^R)
    (ε*δ*Fintype.card (Slots (B:=B) Λ)+δ^2*q^2) hn (by positivity) hrem hr ha₀ hb₀ hF hframe
    (by simpa only [r,run_zero] using hJ) hfJ hf (by simpa only [r,run_zero] using hs) hg hbad
  · intro i j
    have hcn : c i ≤ c n := by
      dsimp only [c,cut]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt.le) _
    have hcu : c i ≤ (n+1)*Q := by
      have hw := warm_le (Q:=Q) t
      dsimp only [c,cut]
      nlinarith [i.isLt]
    convert frame_indexed_localization s ι hι hQ hqQ hdiv Λ edge
      (fun j : Fin q=>a₀ j) (fun j : Fin q=>b₀ j) ha₀ hb₀ a b hab hsite
      P {v | v.1.val∈F} p hp δ hδ.le (fun j hj=>by rw [hrate j hj]; ring_nf; exact le_refl δ)
      t (c i) (n+1) R (hcn.trans hhor) hcu j.val (fun base=>hJ base j.val j.property) using 1
  · intro i
    have h:=hδE hδ.le hδ2 T s a b r c hr hc ha hb p hp hrate' P {v | v.1.val∈F} f hf
      (by simpa only [r,run_zero,swap_classical] using hs) i
    simpa only [swap_classical,exposedSweep_classical,show 2*(δ/2)=δ by ring,add_assoc] using h

end Heisenberg.Flow

end
end

end

end OAI
end

theorem solution : type_of% @OAI.Heisenberg.Flow.indexed_prefix_leakage_oai := @OAI.Heisenberg.Flow.indexed_prefix_leakage_oai
