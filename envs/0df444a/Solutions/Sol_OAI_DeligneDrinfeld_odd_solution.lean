-- Prove2me | solution 1 for OAI.DeligneDrinfeld.odd_solution
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-07T18:54:18.835828+00:00
-- url     : https://prove2.me/submissions/9b4a3073-881a-4ee4-a4f0-efb457de9812

import Mathlib
import Definitions.Def_DeligneDrinfeld
import Definitions.Def_DeligneDrinfeldBraid
import Theorems.Thm_OAI_DeligneDrinfeld_ComplexComparison_real_value_cyclic
import Theorems.Thm_OAI_DeligneDrinfeld_CutoffPrimitiveExtract_KZ_value_lie
import Theorems.Thm_OAI_DeligneDrinfeld_FourFrames_associator_pentagon
import Theorems.Thm_OAI_RealDeligneDrinfeld_BraidInsertionSum_pentagon

set_option linter.all false


section

namespace OAI

noncomputable section
namespace DeligneDrinfeld

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

attribute [local instance 2000] FreeLieAlgebra.instLieAlgebra

namespace IntegralBaseChange
open AssociativeElimination
attribute [local instance] LieRing.ofAssociativeRing
variable {S α : Type*} [CommRing S]
def words : A ℤ α →+* A S α := MonoidAlgebra.mapRingHom _ (Int.castRingHom S)
@[simp] theorem words_atom (a : α) : words (atom a : A ℤ α)=(atom a : A S α) := by
  simp [words,atom]
@[simp] theorem words_coeff (p : A ℤ α) (w : FreeMonoid α) :
    (words p : A S α).coeff w=(p.coeff w : S) := by simp [words]
def lie : FreeLieAlgebra ℤ α →ₗ⁅ℤ⁆ FreeLieAlgebra S α :=
  FreeLieAlgebra.lift ℤ (FreeLieAlgebra.of S)
@[simp] theorem lie_of (a : α) : lie (FreeLieAlgebra.of ℤ a)=FreeLieAlgebra.of S a := by exact FreeLieAlgebra.lift_of_apply (FreeLieAlgebra.of S) a
theorem embed_lie (p : FreeLieAlgebra ℤ α) :
    embed (lie p : FreeLieAlgebra S α)=words (embed p) := by
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => simp
  | ha p q hp hq => simp [hp,hq]
  | hs r p hp => simp [map_smul,hp]
  | hl p q hp hq => simp only [LieHom.map_lie,hp,hq,Ring.lie_def,map_sub,map_mul]

end IntegralBaseChange

namespace BaseChangeEquations
variable {R : Type*} [CommRing R]

variable {S : Type*} [CommRing S]
@[simp] theorem cast_x : IntegralBaseChange.lie (x : FreeLieAlgebra ℤ Bool)=(x : FreeLieAlgebra S Bool) := by simp [x]
@[simp] theorem cast_y : IntegralBaseChange.lie (y : FreeLieAlgebra ℤ Bool)=(y : FreeLieAlgebra S Bool) := by simp [y]

end BaseChangeEquations

namespace WordGrading
open AssociativeElimination
variable {R α : Type*} [CommRing R]
theorem mem_space_iff {P : FreeMonoid α → Prop} {p : A R α} :
    p∈space P ↔ ∀ w,p.coeff w≠0 → P w := by
  constructor
  · intro hp w hw
    by_contra h
    exact hw (coeff_support hp w h)
  · exact mem_space

end WordGrading

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]
variable (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)

theorem algHom_homogeneous (hf : ∀ a,f (atom a)∈homogeneous wb (wa a))
    {n : ℕ} {p : A R α} (hp : p∈homogeneous wa n) : f p∈homogeneous wb n := by
  have hw (w : FreeMonoid α) : f (word w)∈homogeneous wb (degree wa w) := by
    induction w using FreeMonoid.inductionOn' with
    | one =>
      rw [word_one,map_one,degree_one]
      exact word_mem (1 : FreeMonoid β) (degree_one wb)
    | of_mul a w ih =>
      simp only [word_mul,word_of,map_mul,degree_mul,degree_of]
      exact homogeneous_mul (hf a) ih
  apply map_space f.toLinearMap _ ?_ hp
  intro w h
  change f (word w)∈homogeneous wb n
  rw [← h]
  exact hw w

end WordGrading

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
namespace WordGrading
open AssociativeElimination
variable {R α β : Type*} [CommRing R]

theorem project_degree_homogeneous (wt : α → ℕ) (P : ℕ → Prop) [DecidablePred P]
    {k : ℕ} {p : A R α} (hp : p∈homogeneous wt k) :
    project (fun w => P (degree wt w)) p=if P k then p else 0 := by
  by_cases h : P k
  · rw [if_pos h]
    exact project_eq_self (space_mono (by intro w hw; exact hw ▸ h) hp)
  · rw [if_neg h]
    exact project_eq_zero hp (by intro w hw; simpa only [hw] using h)

theorem algHom_project (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (P : ℕ → Prop) [DecidablePred P]
    (p : A R α) :
    f (project (fun w => P (degree wa w)) p)=project (fun w => P (degree wb w)) (f p) := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change f (project _ (word w))=project _ (f (word w))
    rw [project_word,project_degree_homogeneous wb P
      (algHom_homogeneous f wa wb hf (word_mem w rfl))]
    split_ifs <;> simp
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

theorem algHom_piece (f : A R α →ₐ[R] A R β) (wa : α → ℕ) (wb : β → ℕ)
    (hf : ∀ a,f (atom a)∈homogeneous wb (wa a)) (n : ℕ) (p : A R α) :
    f (piece wa n p)=piece wb n (f p) := algHom_project f wa wb hf (fun k => k=n) p

theorem project_preserves {P Q : FreeMonoid α → Prop} [DecidablePred Q]
    {p : A R α} (hp : p∈space P) : project Q p∈space P := by
  apply mem_space
  intro w hw
  rw [project_coeff] at hw
  split_ifs at hw with h
  · exact (mem_space_iff.mp hp) w hw
  · exact (hw rfl).elim

theorem subtract_piece_above {wt : α → ℕ} {n : ℕ} {p : A R α}
    (hp : p∈above wt n) : p-piece wt n p∈above wt (n+1) := by
  apply mem_space
  intro w hw
  change (p-piece wt n p).coeff w≠0 at hw
  simp only [MonoidAlgebra.coeff_sub,Finsupp.sub_apply] at hw
  change p.coeff w-(project (fun w => degree wt w=n) p).coeff w≠0 at hw
  rw [project_coeff] at hw
  have hn : n≤degree wt w := by
    by_contra h
    have hz := coeff_support hp w h
    simp [hz] at hw
  by_cases he : degree wt w=n
  · simp [he] at hw
  · omega
end WordGrading

end

namespace TensorProjection
open AssociativeElimination WordGrading
open scoped TensorProduct
variable {R α β : Type*} [CommRing R]

abbrev len {α : Type*} (w : FreeMonoid α) : ℕ := degree (fun _ => 1) w

end TensorProjection

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace TruncatedWords
open AssociativeElimination WordGrading
variable {R α : Type*} [CommRing R]

variable [Finite α]

variable (P : Set (A ℝ α)) (N : ℕ)

instance normedRing : NormedRing (Q P N) := FiniteAlgebraNorm.normedRing _
instance normedAlgebra : NormedAlgebra ℝ (Q P N) := FiniteAlgebraNorm.normedAlgebra _

end TruncatedWords
end

namespace NilpotentFreeLift
open AssociativeElimination WordGrading TruncatedWords FinitePicard
variable {α B : Type*} [NormedRing B] [NormedAlgebra ℝ B]
variable (F : NilpotentFiltration B) (f : α → B) (hf : ∀ a,f a∈F.space 1)
include hf
 theorem eval_preserves {n : ℕ} {p : Q (∅ : Set (A ℝ α)) F.cutoff}
    (hp : p∈filtration ∅ F.cutoff n) : eval F f hf p∈F.space n := by
  obtain ⟨p,hp,rfl⟩ := hp
  change eval F f hf (quotient ∅ F.cutoff p)∈_
  rw [eval_quotient]
  exact lift_mem F f hf hp
end NilpotentFreeLift

end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

end

section

open AssociativeElimination UniversalEmbedding WordGrading
open scoped TensorProduct

end

namespace LowWeight
open LieGrading UniversalEmbedding

theorem treeDegree_pos {α : Type*} {wt : α → ℕ} (hw : ∀ a,0<wt a) (u : UniversalEmbedding.Tree α) :
    0<treeDegree wt u := by
  induction u with
  | leaf a => simpa using hw a
  | node u v hu hv => simp only [treeDegree_node]; omega

theorem tree_degree_one {α : Type*} (u : UniversalEmbedding.Tree α) (hu : treeDegree (fun _ => 1) u=1) :
    ∃ a,u=.leaf a := by
  cases u with
  | leaf a => exact ⟨a,rfl⟩
  | node u v =>
    have h1 := treeDegree_pos (fun _ : α => Nat.zero_lt_one) u
    have h2 := treeDegree_pos (fun _ : α => Nat.zero_lt_one) v
    simp only [treeDegree_node] at hu
    omega

attribute [local instance] LieRing.ofAssociativeRing

end LowWeight

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section

namespace FinitePicard
open MeasureTheory Set intervalIntegral
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]
variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_term (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (term Ω a N t)=term (fun s => f (Ω s)) a N t := by
  induction N generalizing t with
  | zero => simp
  | succ N ih =>
    rw [term_succ,term_succ]
    let fc := f.toLinearMap.toContinuousLinearMap
    have hi' : IntervalIntegrable (fun s => Ω s * term Ω a N s) volume a t :=
      (hi.mul_continuousOn (continuousOn_term hi N)).mono_set (uIcc_subset_uIcc_left ht)
    change fc (∫ s in a..t, Ω s * term Ω a N s)=_
    rw [←fc.intervalIntegral_comp_comm hi']
    apply intervalIntegral.integral_congr
    intro s hs
    have hst : s ∈ uIcc a b := uIcc_subset_uIcc_left ht hs
    change f (Ω s*term Ω a N s)=f (Ω s)*term (fun s => f (Ω s)) a N s
    rw [map_mul,ih hst]

theorem map_transport (f : A →ₐ[ℝ] B) {Ω : ℝ → A} {a b : ℝ}
    (hi : IntervalIntegrable Ω volume a b) (N : ℕ) {t : ℝ} (ht : t ∈ uIcc a b) :
    f (transport Ω a N t)=transport (fun s => f (Ω s)) a N t := by
  simp only [transport,map_sum]
  exact Finset.sum_congr rfl (fun n _ => map_term f hi n ht)

end FinitePicard

namespace KZCollar
open MeasureTheory Set Filter FinitePicard
variable {A B : Type*} [NormedRing A] [NormedAlgebra ℝ A] [NormedRing B] [NormedAlgebra ℝ B]

theorem map_gauge (f : A →ₐ[ℝ] B) (X : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (gauge X s)=gauge (f X) s := by
  have hY : (f X)^(N+1)=0 := by rw [←map_pow,hX,map_zero]
  rw [gauge_finite X hX,gauge_finite (f X) hY]
  simp only [map_sum,map_smul,map_pow]

theorem map_regularForm (f : A →ₐ[ℝ] B) (X Y : A) {N : ℕ} (hX : X^(N+1)=0) (s : ℝ) :
    f (regularForm X Y s)=regularForm (f X) (f Y) s := by
  have hN : (-X)^(N+1)=0 := by rw [neg_pow,hX,mul_zero]
  simp only [regularForm,map_mul,map_smul,map_gauge f X hX,map_gauge f (-X) hN,map_neg]

variable [FiniteDimensional ℝ A] [CompleteSpace B]

theorem map_normalizedSolution (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X : A} (hX : X ∈ F.space 1) (Y : A) {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    f (normalizedSolution F X Y s)=normalizedSolution G (f X) (f Y) s := by
  have hi := regularForm_integrable X Y (pow_cutoff_eq_zero F hX) hs hs1
  simp only [normalizedSolution,map_mul,map_gauge f X (pow_cutoff_eq_zero F hX)]
  rw [map_transport f hi F.cutoff right_mem_uIcc,hN]
  have hh : (fun s => f (regularForm X Y s))=regularForm (f X) (f Y) := by
    funext s
    exact map_regularForm f X Y (pow_cutoff_eq_zero F hX) s
  rw [hh]

omit [FiniteDimensional ℝ A] [CompleteSpace B] in
theorem map_unit_inverse (f : A →ₐ[ℝ] B) {x : A} (hx : IsUnit x) :
    f (Ring.inverse x)=Ring.inverse (f x) := by
  calc
    f (Ring.inverse x)=f (Ring.inverse x)*(f x*Ring.inverse (f x)) := by
      rw [Ring.mul_inverse_cancel _ (hx.map f),mul_one]
    _ = (f (Ring.inverse x)*f x)*Ring.inverse (f x) := (mul_assoc _ _ _).symm
    _ = Ring.inverse (f x) := by rw [←map_mul,Ring.inverse_mul_cancel _ hx,map_one,one_mul]

variable [CompleteSpace A]

theorem map_associator (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B) (hN : F.cutoff=G.cutoff)
    {X Y : A} (hX : X ∈ F.space 1) (hY : Y ∈ F.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  rw [associator,map_mul,map_unit_inverse f (rightSolution_isUnit F hX hY (1/2))]
  unfold rightSolution
  rw [map_normalizedSolution f F G hN hY X (by norm_num) (by norm_num),
    map_normalizedSolution f F G hN hX Y (by norm_num) (by norm_num)]
  rfl

end KZCollar

end

section
namespace FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]

 theorem term_above_cutoff (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t,Ω t∈F.space 1) {n : ℕ} (hn : F.cutoff<n) (a t : ℝ) : term Ω a n t=0 := by
  have h := F.antitone hn (term_mem F hΩ a n t)
  simpa only [F.terminal,Submodule.mem_bot] using h

 theorem stabilize (F : NilpotentFiltration A) {Ω : ℝ → A}
    (hΩ : ∀ t,Ω t∈F.space 1) {N : ℕ} (hn : F.cutoff ≤ N) (a t : ℝ) :
    transport Ω a N t=transport Ω a F.cutoff t := by
  unfold transport
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right hn 1))
  intro n hnN hnc
  rw [Finset.mem_range,not_lt] at hnc
  exact term_above_cutoff F hΩ (by omega) a t

 def extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N) : NilpotentFiltration A where
  space := F.space
  antitone := F.antitone
  one_mem := F.one_mem
  mul_mem := F.mul_mem
  cutoff := N
  terminal := le_antisymm (le_trans (F.antitone (Nat.add_le_add_right hN 1)) F.terminal.le) bot_le

end FinitePicard
namespace KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A] [CompleteSpace A]

 omit [CompleteSpace A] in
 theorem normalized_extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) (s : ℝ) :
    normalizedSolution (extend F N hN) X Y s=normalizedSolution F X Y s := by
  simp only [normalizedSolution,extend]
  rw [stabilize F (regularForm_mem F hX hY) hN]

 omit [CompleteSpace A] in
 theorem associator_extend (F : NilpotentFiltration A) (N : ℕ) (hN : F.cutoff ≤ N)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator (extend F N hN) X Y=associator F X Y := by
  simp only [associator,rightSolution,normalized_extend F N hN hX hY,
    normalized_extend F N hN hY hX]

 variable {B : Type*} [NormedRing B] [NormedAlgebra ℝ B] [FiniteDimensional ℝ B] [CompleteSpace B]

 theorem map_associator_general (f : A →ₐ[ℝ] B)
    (F : NilpotentFiltration A) (G : NilpotentFiltration B)
    {X Y : A} (hX : X∈F.space 1) (hY : Y∈F.space 1)
    (hfX : f X∈G.space 1) (hfY : f Y∈G.space 1) :
    f (associator F X Y)=associator G (f X) (f Y) := by
  let N := max F.cutoff G.cutoff
  rw [←associator_extend F N (le_max_left _ _) hX hY,
    ←associator_extend G N (le_max_right _ _) hfX hfY]
  exact map_associator f (extend F N (le_max_left _ _))
    (extend G N (le_max_right _ _)) rfl hX hY

end KZCollar

end

namespace CutoffDiagonal
open scoped TensorProduct
open CutoffDepth CutoffKZ FinitePicard
local instance (N : ℕ) : NormedRing (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (Q ℝ N⊗[ℝ]Q ℝ N) := FiniteAlgebraNorm.normedAlgebra _

def drop (M N : ℕ) (h : N ≤ M) : Q ℝ M →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (extend (weight N) M h) (gen N) (gen_weight N)
 @[simp] theorem drop_gen (M N : ℕ) (h : N ≤ M) (b : Bool) : drop M N h (gen M b)=gen N b :=
  NilpotentFreeLift.eval_gen _ _ _ b
 theorem drop_mem (M N : ℕ) (h : N ≤ M) (n : ℕ) (u : Q ℝ M) (hu : u∈(weight M).space n) :
    drop M N h u∈(weight N).space n :=
  NilpotentFreeLift.eval_preserves (extend (weight N) M h) (gen N) (gen_weight N) hu
 theorem drop_associator (M N : ℕ) (h : N ≤ M) :
    drop M N h (KZCollar.associator (weight M) (X M) (Y M))=KZCollar.associator (weight N) (X N) (Y N) := by
  rw [KZCollar.map_associator_general (drop M N h) (weight M) (weight N)
    (gen_weight M false) (gen_weight M true)
    (drop_mem M N h 1 _ (gen_weight M false)) (drop_mem M N h 1 _ (gen_weight M true)),
    drop_gen,drop_gen]
end CutoffDiagonal

namespace CutoffKZ
open CutoffDepth FinitePicard KZCollar MeasureTheory Set Filter
open scoped Topology

theorem associator_coefficient_ne_zero (N m : ℕ) (hN : m+1 ≤ N) (hm : 0 < m) :
    c N m (associator (weight N) (X N) (Y N))≠0 := by
  rw [associator_coefficient N m hN hm]
  exact DepthIntegral.coefficient_ne_zero m hm

end CutoffKZ

namespace ConjugateComparison

section
open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem inverse_normalized (P : Qˣ) (hP : (P:Q)-1∈F 1) : ((P⁻¹:Qˣ):Q)-1∈F 1 := by
  have h := filtration_mul ∅ N 0 1 (mem_zero N ((P⁻¹:Qˣ):Q)) hP
  have he : ((P⁻¹:Qˣ):Q)*((P:Q)-1)=-(((P⁻¹:Qˣ):Q)-1) := by
    rw [mul_sub,Units.inv_mul,mul_one,neg_sub]
  rw [he] at h
  exact (F 1).neg_mem_iff.mp h

theorem exact_comparison (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)*theta N P V hP hV (P:Q)=(V:Q) := by
  change ((V:Q)*((Units.map (theta N P V hP hV).toMonoidHom P)⁻¹:Qˣ))*
    (Units.map (theta N P V hP hV).toMonoidHom P:Q)=(V:Q)
  rw [mul_assoc,Units.inv_mul,mul_one]

theorem theta_transport (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) (u : Q) :
    theta N P V hP hV (transport N P hP u)=transport N V hV u := by
  exact congrArg (transport N V hV) ((transport N P hP).symm_apply_apply u)

theorem theta_x (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    theta N P V hP hV (gen N false)=gen N false := by
  simpa only [transport_gen,family] using theta_transport N P V hP hV (gen N false)

theorem theta_y (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    theta N P V hP hV (gen N true)=
      (((unitArrow N P V hP hV)⁻¹:Qˣ):Q)*gen N true*(unitArrow N P V hP hV:Q) := by
  have hh := theta_transport N P V hP hV (gen N true)
  simp only [transport_gen,family,map_mul] at hh
  let M := Units.map (theta N P V hP hV).toMonoidHom P
  have h : ((M⁻¹:Qˣ):Q)*theta N P V hP hV (gen N true)*(M:Q)=
      ((V⁻¹:Qˣ):Q)*gen N true*(V:Q) := hh
  have hh := congrArg (fun z : Q => (M:Q)*z*((M⁻¹:Qˣ):Q)) h
  simp only [mul_assoc,Units.mul_inv_cancel_left] at hh
  simpa only [unitArrow,mul_inv_rev,inv_inv,Units.val_mul,M,mul_assoc,Units.mul_inv,mul_one] using hh

end

open AssociativeElimination TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R Bool)) N
local notation "F" => filtration (∅ : Set (A R Bool)) N

theorem transport_raises (P : Qˣ) (hP : (P:Q)-1∈F 1) (n : ℕ) (u : Q) (hu : u∈F n) :
    transport N P hP u-u∈F (n+1) :=
  subst_raises N (family N P) (family_mem N P) (family_leading N P hP) n u hu

theorem transport_inverse_preserves (P : Qˣ) (hP : (P:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : (transport N P hP).symm u∈F n := by
  have hh : ∀ k≤n,(transport N P hP).symm u∈F k := by
    intro k
    induction k with
    | zero => intro _; exact mem_zero N _
    | succ k ih =>
      intro hk
      have hd := transport_raises N P hP k _ (ih (by omega))
      rw [AlgEquiv.apply_symm_apply] at hd
      have he := (F (k+1)).sub_mem (filtration_antitone ∅ N hk hu) hd
      simpa only [sub_sub_cancel] using he
  exact hh n le_rfl

theorem theta_raises (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u-u∈F (n+1) := by
  have hh := transport_inverse_preserves N P hP n u hu
  have hd := (F (n+1)).sub_mem (transport_raises N V hV n _ hh)
    (transport_raises N P hP n _ hh)
  simpa only [sub_sub_sub_cancel_right,AlgEquiv.apply_symm_apply,theta,AlgEquiv.trans_apply] using hd

theorem theta_preserves (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1)
    (n : ℕ) (u : Q) (hu : u∈F n) : theta N P V hP hV u∈F n := by
  have h := (F n).add_mem (filtration_antitone ∅ N (Nat.le_succ n)
    (theta_raises N P V hP hV n u hu)) hu
  simpa only [sub_add_cancel] using h

theorem mul_normalized (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    ((P*V:Qˣ):Q)-1∈F 1 := by
  have h := (F 1).add_mem
    (filtration_mul ∅ N 1 0 hP (mem_zero N (V:Q))) hV
  simpa only [sub_mul,one_mul,sub_add_sub_cancel,Units.val_mul] using h

theorem unitArrow_normalized (P V : Qˣ) (hP : (P:Q)-1∈F 1) (hV : (V:Q)-1∈F 1) :
    (unitArrow N P V hP hV:Q)-1∈F 1 := by
  apply mul_normalized N V _ hV
  apply inverse_normalized N
  change theta N P V hP hV (P:Q)-1∈_
  simpa only [map_sub,map_one] using theta_preserves N P V hP hV 1 ((P:Q)-1) hP

end ConjugateComparison

namespace CutoffScaling
open AssociativeElimination WordGrading TruncatedWords TruncatedSubstitution
variable {R : Type*} [CommRing R] {α : Type*} (N : ℕ)
local notation "Q" => TruncatedWords.Q (∅ : Set (A R α)) N

 theorem map_word (r : R) (w : FreeMonoid α) :
    map N r (quotient ∅ N (word w))=r^(degree wt w) • quotient ∅ N (word w) := by
  rw [map,subst_quotient,lift_word]

 theorem coefficient (r : R) (w : FreeMonoid α) (u : Q) :
    TruncatedFree.coefficient N w (map N r u)=r^(degree wt w)*TruncatedFree.coefficient N w u := by
  classical
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  change TruncatedFree.coefficient N w (map N r (quotient ∅ N p))=_
  induction p using MonoidAlgebra.induction_on with
  | of v =>
    change TruncatedFree.coefficient N w (map N r (quotient ∅ N (word v)))=r^(degree wt w)*TruncatedFree.coefficient N w (quotient ∅ N (word v))
    rw [map_word,map_smul]
    simp only [TruncatedFree.coefficient_quotient,smul_eq_mul]
    by_cases he : v=w
    · subst v; rfl
    · have hn : (word (R:=R) v).coeff w=0 := by simp [word,he]
      simp only [hn,ite_self,mul_zero]
  | add p q hp hq => simp only [map_add,hp,hq,mul_add]
  | smul s p hp => simp only [map_smul,hp,smul_eq_mul]; ring

end CutoffScaling

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace OperatorLog

section
open Polynomial

variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem sum_range_extend {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n m : ℕ} (h : n ≤ m)
    (hz : ∀ k,n ≤ k → k < m → f k=0) :
    ∑ k∈Finset.range n,f k=∑ k∈Finset.range m,f k := by
  apply Finset.sum_subset (Finset.range_mono h)
  intro k hkm hkn
  exact hz k (Nat.le_of_not_lt (by simpa using hkn)) (Finset.mem_range.mp hkm)

theorem interpolate_nat (N : ℕ) (T : Module.End ℚ V) (hT : T^(N+1)=0) (m : ℕ) :
    interpolate N T m=(1+T)^m := by
  have hpow : ∀ k,N+1 ≤ k → T^k=0 := fun k hk => by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add,hT,zero_mul]
  have hsmall : ∀ k,m+1 ≤ k → (m.choose k : ℚ) • T^k=0 := by
    intro k hk
    rw [Nat.choose_eq_zero_of_lt (by omega),Nat.cast_zero,zero_smul]
  unfold interpolate
  simp only [binom_eval_nat]
  rw [sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (m:=N+m+2) (by omega)
    (fun k hk _ => by rw [hpow k hk,smul_zero])]
  rw [←sum_range_extend (fun k => (m.choose k : ℚ) • T^k) (n:=m+1) (m:=N+m+2) (by omega)
    (fun k hk _ => hsmall k hk)]
  rw [add_comm (1:Module.End ℚ V) T,(Commute.one_right T).add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [one_pow,mul_one,Algebra.smul_def,map_natCast]
  exact Nat.cast_comm _ _

def valuePolynomial (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ k∈Finset.range (N+1),binom k*C (l ((T^k) a))

theorem value_eval (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) (s : ℚ) :
    (valuePolynomial N T a l).eval s=l (interpolate N T s a) := by
  simp [valuePolynomial,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,Polynomial.eval_finsetSum]

theorem value_one (N : ℕ) (T : Module.End ℚ V) (a : V) (l : V →ₗ[ℚ] ℚ) :
    (valuePolynomial N T a l).coeff 1=l (logarithm N T a) := by
  simp [valuePolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply]

theorem polynomial_ext_nat {p q : ℚ[X]} (h : ∀ n : ℕ,p.eval (n:ℚ)=q.eval (n:ℚ)) : p=q := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply (Set.infinite_range_of_injective (Nat.cast_injective (R:=ℚ))).mono
  rintro _ ⟨n,rfl⟩
  exact h n

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

def pairPolynomial (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) : ℚ[X] :=
  ∑ i∈Finset.range (N+1),∑ j∈Finset.range (N+1),
    (binom i*binom j)*C (l (B ((T^i) a) ((S^j) b)))

theorem pair_eval (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) (s : ℚ) :
    (pairPolynomial N T S B a b l).eval s=
      l (B (interpolate N T s a) (interpolate N S s b)) := by
  simp only [pairPolynomial,Polynomial.eval_finsetSum,eval_mul,eval_C,interpolate,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,smul_eq_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem pair_one (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (a : V) (b : W) (l : U →ₗ[ℚ] ℚ) :
    (pairPolynomial N T S B a b l).coeff 1=
      l (B (logarithm N T a) b+B a (logarithm N S b)) := by
  simp [pairPolynomial,logarithm,LinearMap.sum_apply,LinearMap.smul_apply,mul_coeff_one,
    binom_coeff_zero,add_mul,Finset.sum_add_distrib,ite_mul,mul_ite,add_comm]

theorem powers_bilinear (A : Module.End ℚ V) (C : Module.End ℚ W) (D : Module.End ℚ U)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U) (h : ∀ a b,D (B a b)=B (A a) (C b)) (m : ℕ) (a : V) (b : W) :
    (D^m) (B a b)=B ((A^m) a) ((C^m) b) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    simp only [pow_succ',Module.End.mul_apply,ih,h]

theorem logarithm_bilinear (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (R : Module.End ℚ U) (hT : T^(N+1)=0) (hS : S^(N+1)=0) (hR : R^(N+1)=0)
    (B : V →ₗ[ℚ] W →ₗ[ℚ] U)
    (h : ∀ a b,(1+R) (B a b)=B ((1+T) a) ((1+S) b)) (a : V) (b : W) :
    logarithm N R (B a b)=B (logarithm N T a) b+B a (logarithm N S b) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ
    (logarithm N R (B a b)-(B (logarithm N T a) b+B a (logarithm N S b)))).mp
  intro l
  have hp : valuePolynomial N R (B a b) l=pairPolynomial N T S B a b l := by
    apply polynomial_ext_nat
    intro m
    rw [value_eval,pair_eval,interpolate_nat N R hR,interpolate_nat N T hT,interpolate_nat N S hS]
    exact congrArg l (powers_bilinear _ _ _ B h m a b)
  have hc := congrArg (fun p : ℚ[X] => p.coeff 1) hp
  rw [value_one,pair_one] at hc
  simpa only [map_sub,sub_eq_zero] using hc

end

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

theorem powers_natural (T : Module.End ℚ V) (S : Module.End ℚ W) (f : V →ₗ[ℚ] W)
    (h : ∀ v,f (T v)=S (f v)) (n : ℕ) (v : V) : f ((T^n) v)=(S^n) (f v) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pow_succ',Module.End.mul_apply,h,ih]

theorem logarithm_natural (N : ℕ) (T : Module.End ℚ V) (S : Module.End ℚ W)
    (f : V →ₗ[ℚ] W) (h : ∀ v,f (T v)=S (f v)) (v : V) :
    f (logarithm N T v)=logarithm N S (f v) := by
  simp only [logarithm,LinearMap.sum_apply,LinearMap.smul_apply,map_sum,map_smul,
    powers_natural T S f h]

end OperatorLog

namespace LogCategory
open OperatorLog
variable {A O : Type*} [Ring A] [Algebra ℚ A]

theorem delta_comp (g : Data A O) (p q r : O) (a b : A) :
    delta g p r (b*a)=delta g q r b*a+b*delta g p q a := by
  apply logarithm_bilinear g.N (g.S q r-1) (g.S p q-1) (g.S p r-1)
    (g.nilpotent q r) (g.nilpotent p q) (g.nilpotent p r) (LinearMap.mul ℚ A)
  intro b a
  have he : ∀ p q,(1+(g.S p q-1))=g.S p q := by intros; abel
  simpa only [he,LinearMap.mul_apply'] using g.comp p q r a b

attribute [local instance] LieRing.ofAssociativeRing

theorem unit_cocycle (g : Data A O) (p q r : O) :
    delta g p r 1=delta g q r 1+delta g p q 1 := by
  simpa only [one_mul,mul_one] using delta_comp g p q r 1 1

theorem delta_formula (g : Data A O) (o p q : O) (u : A) :
    delta g p q u=delta g o o u+delta g o q 1*u-u*delta g o p 1 := by
  have h₁ := delta_comp g o p q 1 u
  have h₂ := delta_comp g o o q u 1
  simp only [mul_one,one_mul] at h₁ h₂
  rw [h₂] at h₁
  exact eq_sub_of_add_eq (by simpa only [add_comm] using h₁.symm)

end LogCategory

namespace OperatorLog
variable {A : Type*} [Ring A] [Algebra ℚ A]

theorem logarithm_depth_one (F : ℕ → Submodule ℚ A) (hF : Antitone F)
    (T : Module.End ℚ A) (hT : ∀ n u,u∈F n → T u∈F (n+1))
    (h1 : (1:A)∈F 0) (N : ℕ) :
    logarithm (N+1) T 1-T 1∈F 2 := by
  have hp : ∀ k,(T^k) 1∈F k := by
    intro k
    induction k with
    | zero => exact h1
    | succ k ih => simpa only [pow_succ',Module.End.mul_apply] using hT k _ ih
  rw [logarithm_eq]
  rw [Finset.sum_range_succ']
  simp only [LinearMap.add_apply,LinearMap.sum_apply,LinearMap.smul_apply,
    pow_zero,Nat.cast_zero,zero_add,div_one,one_smul,pow_one,add_sub_cancel_right]
  apply Submodule.sum_mem
  intro k hk
  exact Submodule.smul_mem _ _ (hF (by omega : 2≤k+1+1) (hp _))

theorem comparison_depth_one (F : ℕ → Submodule ℚ A) (hF : Antitone F)
    (hmul : ∀ i j {u v : A},u∈F i → v∈F j → u*v∈F (i+j))
    (θ : A →ₐ[ℚ] A) (hθ : ∀ n u,u∈F n → θ u-u∈F (n+1))
    {U Φ Ψ : A} (hU : U-1∈F 1) (hΦ : Φ-1∈F 1) (h : U*θ Φ=Ψ) :
    Ψ-Φ-(U-1)∈F 2 := by
  have hd : θ Φ-Φ∈F 2 := by
    simpa only [map_sub,map_one,sub_sub_sub_cancel_right] using hθ 1 (Φ-1) hΦ
  have hθΦ : θ Φ-1∈F 1 := by
    simpa only [sub_add_sub_cancel] using (F 1).add_mem (hF (by omega : 1≤2) hd) hΦ
  have hh := hmul 1 1 hU hθΦ
  have he : Ψ-Φ-(U-1)=(U-1)*(θ Φ-1)+(θ Φ-Φ) := by
    rw [←h]
    noncomm_ring
  rw [he]
  exact (F 2).add_mem hh hd

end OperatorLog

namespace KZComparison
open CutoffDepth CutoffKZ FinitePicard KZCollar

 theorem negative_val (N : ℕ) : (negative N:Q ℝ N)=associator (weight N) (-X N) (-Y N) := by
  change CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N)=_
  rw [positive_val,map_associator _ (weight N) (weight N) rfl (gen_weight N false) (gen_weight N true)]
  have h (b : Bool) : CutoffScaling.map N (-1:ℝ) (gen N b)= -gen N b := by
    simpa only [neg_smul,one_smul,gen,TruncatedSubstitution.gen] using CutoffScaling.map_gen N (-1:ℝ) b
  rw [h false,h true]

 theorem exact_comparison (N : ℕ) : (arrow N:Q ℝ N)*theta N (positive N:Q ℝ N)=(negative N:Q ℝ N) :=
  ConjugateComparison.exact_comparison N _ _ _ _

 theorem theta_x (N : ℕ) : theta N (X N)=X N := ConjugateComparison.theta_x N _ _ _ _
 theorem theta_y (N : ℕ) : theta N (Y N)=((arrow N)⁻¹:(Q ℝ N)ˣ)*Y N*(arrow N:Q ℝ N) :=
  ConjugateComparison.theta_y N _ _ _ _

 theorem arrow_log_congruence (N : ℕ) : value N-((arrow N:Q ℝ N)-1)∈depthSpace N 2 := by
  have hh := OperatorLog.logarithm_depth_one (A:=Q ℝ N) (rationalDepth N) (depth_antitone N)
    ((category N).S false true-(1 : Module.End ℚ (Q ℝ N)))
    (GaugeAutomorphism.raises ((theta N).restrictScalars ℚ) (frames N) (rationalDepth N)
      (depth_antitone N) (rationalDepth_initial N) (depth_mul N) (theta_depth N) (frames_depth N) false true)
    (depth_one N) N
  simpa only [rationalDepth,Submodule.restrictScalars_mem,value,LogCategory.delta,category,GaugeAutomorphism.data,LinearMap.sub_apply,
    Module.End.one_apply,GaugeAutomorphism.map_apply,frames,inv_one,Units.val_one,map_one,mul_one] using hh

 theorem comparison_congruence (N : ℕ) :
    (negative N:Q ℝ N)-(positive N:Q ℝ N)-value N∈depthSpace N 2 := by
  have hh := OperatorLog.comparison_depth_one (rationalDepth N) (depth_antitone N)
    (depth_mul N) ((theta N).restrictScalars ℚ).toAlgHom (theta_depth N)
    (arrow_depth N) (positive_depth N) (exact_comparison N)
  have hd := (depthSpace N 2).sub_mem hh (arrow_log_congruence N)
  simpa only [sub_sub_sub_cancel_right] using hd

 theorem value_coefficient (N m : ℕ) :
    c N m (value N)=((-1:ℝ)^(m+1)-1)*c N m (positive N:Q ℝ N) := by
  have hh := coeff_zero_of_depth N 2 (comparison_congruence N)
    (w:=GenericIhara.depthOneWord m) (by simp [GenericIhara.depthOneWord,GenericIhara.depth])
  change c N m ((negative N:Q ℝ N)-(positive N:Q ℝ N)-value N)=0 at hh
  rw [map_sub,map_sub] at hh
  have hn : c N m (negative N:Q ℝ N)=(-1:ℝ)^(m+1)*c N m (positive N:Q ℝ N) := by
    change TruncatedFree.coefficient N (GenericIhara.depthOneWord m)
      (CutoffScaling.map N (-1:ℝ) (positive N:Q ℝ N))=_
    simpa only [length_depthOne,c] using CutoffScaling.coefficient N (-1:ℝ)
      (GenericIhara.depthOneWord m) (positive N:Q ℝ N)
  rw [hn] at hh
  linear_combination -hh

 theorem odd_value_nonzero (k : ℕ) : c (2*k+3) (2*k+2) (value (2*k+3))≠0 := by
  rw [value_coefficient]
  have hp : (-1:ℝ)^(2*k+2+1)= -1 := Odd.neg_one_pow ⟨k+1,by omega⟩
  rw [hp]
  apply mul_ne_zero (by norm_num)
  rw [positive_val]
  exact associator_coefficient_ne_zero _ _ (by omega) (by omega)

end KZComparison

namespace TruncatedSubstitution
open AssociativeElimination TruncatedWords
variable {R α B : Type*} [CommRing R] [Ring B] [Algebra R B]
 theorem hom_ext (N : ℕ) (f g : Q (∅ : Set (A R α)) N →ₐ[R] B)
    (h : ∀ a,f (gen N a)=g (gen N a)) : f=g := by
  have he : f.comp (quotient ∅ N)=g.comp (quotient ∅ N) := by
    apply AssociativeElimination.hom_ext
    exact h
  apply AlgHom.ext
  intro u
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations (∅ : Set (A R α)) N) u
  exact AlgHom.congr_fun he p
end TruncatedSubstitution

namespace ConjugateCoalgebra
open scoped TensorProduct
open CutoffDepth CutoffKZ CutoffDiagonal ConjugateComparison

theorem transport_cutoff_gen (N : ℕ) (P : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1) (b : Bool) :
    transport N P hP (gen N b)=family N P b := transport_gen N P hP b

theorem natural_inverse {A B : Type*} [Ring A] [Ring B] [Algebra ℝ A] [Algebra ℝ B]
    (f : A →ₐ[ℝ] B) (e : A ≃ₐ[ℝ] A) (d : B ≃ₐ[ℝ] B)
    (he : ∀ u,f (e u)=d (f u)) (u : A) : f (e.symm u)=d.symm (f u) := by
  apply d.injective
  rw [d.apply_symm_apply,←he,e.apply_symm_apply]

end ConjugateCoalgebra

namespace OperatorLog

section
open scoped TensorProduct
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

theorem logarithm_stable (T : Module.End ℚ V) {N M : ℕ} (hT : T^(N+1)=0) (hNM : N≤M) :
    logarithm N T=logarithm M T := by
  unfold logarithm
  apply sum_range_extend _ (by omega : N+1≤M+1)
  intro k hk hkm
  rw [pow_eq_zero_of_le hk hT,smul_zero]

end

variable {V W Z : Type*} [AddCommGroup V] [Module ℚ V]
  [AddCommGroup W] [Module ℚ W] [AddCommGroup Z] [Module ℚ Z]

end OperatorLog

namespace KZPrimitiveValue
open scoped TensorProduct
open CutoffDepth CutoffKZ CutoffDiagonal KZComparison

 def S (N : ℕ) : Module.End ℝ (Q ℝ N) :=
  (LinearMap.mulLeft ℝ (arrow N:Q ℝ N)).comp (theta N).toLinearMap
 @[simp] theorem S_apply (N : ℕ) (u : Q ℝ N) : S N u=(arrow N:Q ℝ N)*theta N u := rfl

end KZPrimitiveValue

namespace KZCutoffComparison
open CutoffDepth CutoffKZ CutoffDiagonal KZComparison ConjugateComparison

 theorem transport_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P : (Q ℝ M)ˣ) (p : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (u : Q ℝ M) :
    f (transport M P hP u)=transport N p hp (f u) := by
  have hv : f (P:Q ℝ M)=(p:Q ℝ N) := congrArg Units.val h
  have hi : f ((P⁻¹:(Q ℝ M)ˣ):Q ℝ M)=((p⁻¹:(Q ℝ N)ˣ):Q ℝ N) :=
    congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) h
  have he : f.comp (transport M P hP).toAlgHom=(transport N p hp).toAlgHom.comp f := by
    apply TruncatedSubstitution.hom_ext M
    intro b
    change f (transport M P hP (gen M b))=transport N p hp (f (gen M b))
    rw [ConjugateCoalgebra.transport_cutoff_gen,hgen,ConjugateCoalgebra.transport_cutoff_gen]
    cases b
    · exact hgen false
    · change f (((P⁻¹:(Q ℝ M)ˣ):Q ℝ M)*gen M true*(P:Q ℝ M))=_
      rw [map_mul,map_mul,hi,hv,hgen]
      rfl
  exact AlgHom.congr_fun he u

 theorem theta_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P V : (Q ℝ M)ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hV : (V:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (k : Units.map f.toMonoidHom V=v) (u : Q ℝ M) :
    f (ConjugateComparison.theta M P V hP hV u)=ConjugateComparison.theta N p v hp hv (f u) := by
  rw [ConjugateComparison.theta,AlgEquiv.trans_apply,transport_natural M N f hgen V v hV hv k,
    ConjugateCoalgebra.natural_inverse f (transport M P hP) (transport N p hp)
      (transport_natural M N f hgen P p hP hp h)]
  rfl

 theorem arrow_natural (M N : ℕ) (f : Q ℝ M →ₐ[ℝ] Q ℝ N)
    (hgen : ∀ b,f (gen M b)=gen N b) (P V : (Q ℝ M)ˣ) (p v : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hV : (V:Q ℝ M)-1∈TruncatedWords.filtration ∅ M 1)
    (hp : (p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hv : (v:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (h : Units.map f.toMonoidHom P=p) (k : Units.map f.toMonoidHom V=v) :
    Units.map f.toMonoidHom (unitArrow M P V hP hV)=unitArrow N p v hp hv := by
  have ht : Units.map f.toMonoidHom (Units.map (ConjugateComparison.theta M P V hP hV).toMonoidHom P)=
      Units.map (ConjugateComparison.theta N p v hp hv).toMonoidHom p := by
    apply Units.ext
    change f (ConjugateComparison.theta M P V hP hV (P:Q ℝ M))=_
    rw [theta_natural M N f hgen P V p v hP hV hp hv h k,show f (P:Q ℝ M)=(p:Q ℝ N) from congrArg Units.val h]
    rfl
  simp only [unitArrow,map_mul,map_inv,k,ht]

 theorem positive_drop (M N : ℕ) (h : N≤M) :
    Units.map (drop M N h).toMonoidHom (positive M)=positive N := by
  apply Units.ext
  change drop M N h (positive M:Q ℝ M)=(positive N:Q ℝ N)
  rw [positive_val,positive_val,drop_associator]
 theorem negative_drop (M N : ℕ) (h : N≤M) :
    Units.map (drop M N h).toMonoidHom (negative M)=negative N := by
  apply Units.ext
  change drop M N h (negative M:Q ℝ M)=(negative N:Q ℝ N)
  rw [negative_val,negative_val,KZCollar.map_associator_general (drop M N h) (weight M) (weight N)
    ((weight M).space 1|>.neg_mem (gen_weight M false)) ((weight M).space 1|>.neg_mem (gen_weight M true))
    (by simpa only [map_neg,drop_gen] using ((weight N).space 1).neg_mem (gen_weight N false))
    (by simpa only [map_neg,drop_gen] using ((weight N).space 1).neg_mem (gen_weight N true)),map_neg,map_neg,drop_gen,drop_gen]

 theorem theta_drop (M N : ℕ) (h : N≤M) (u : Q ℝ M) :
    drop M N h (KZComparison.theta M u)=KZComparison.theta N (drop M N h u) :=
  theta_natural M N (drop M N h) (drop_gen M N h) _ _ _ _ _ _ _ _
    (positive_drop M N h) (negative_drop M N h) u
 theorem arrow_drop (M N : ℕ) (h : N≤M) : Units.map (drop M N h).toMonoidHom (arrow M)=arrow N :=
  arrow_natural M N (drop M N h) (drop_gen M N h) _ _ _ _ _ _ _ _
    (positive_drop M N h) (negative_drop M N h)
 theorem S_drop (M N : ℕ) (h : N≤M) (u : Q ℝ M) :
    drop M N h ((category M).S false true u)=(category N).S false true (drop M N h u) := by
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,frames,inv_one,
    Units.val_one,mul_one]
  change drop M N h ((arrow M:Q ℝ M)*KZComparison.theta M u)=_
  rw [map_mul,theta_drop,show drop M N h (arrow M:Q ℝ M)=(arrow N:Q ℝ N) from congrArg Units.val (arrow_drop M N h)]
  rfl
 theorem value_drop (M N : ℕ) (h : N≤M) : drop M N h (value M)=value N := by
  have hn : ∀ u,drop M N h (((category M).S false true-1) u)=
      ((category N).S false true-1) (drop M N h u) := by
    intro u
    simp only [LinearMap.sub_apply,Module.End.one_apply,map_sub,S_drop]
  have hh := OperatorLog.logarithm_natural (M+1) ((category M).S false true-1)
    ((category N).S false true-1) ((drop M N h).toLinearMap.restrictScalars ℚ) hn 1
  rw [←OperatorLog.logarithm_stable _ ((category N).nilpotent false true) (by omega : N+1≤M+1)] at hh
  change drop M N h (value M)=OperatorLog.logarithm (N+1) _ (drop M N h 1) at hh
  rw [map_one] at hh
  exact hh

end KZCutoffComparison

namespace CutoffPrimitiveExtract
open AssociativeElimination WordGrading TensorProjection
open scoped TensorProduct
variable {R α : Type*} [CommRing R]

theorem piece_trunc (N n : ℕ) (hn : n≤N) (p : A R α) : piece n (truncVal N p)=piece n p := by
  induction p using MonoidAlgebra.induction_on with
  | of w =>
    change piece n (project (fun w => len w≤N) (word w))=piece n (word w)
    rw [project_word]
    by_cases hw : len w≤N
    · rw [if_pos hw]
    · rw [if_neg hw,map_zero,TensorProjection.piece,WordGrading.piece,project_word,if_neg (by change len w≠n; omega)]
  | add p q hp hq => simp only [map_add,hp,hq]
  | smul c p hp => simp only [map_smul,hp]

open CutoffDepth CutoffKZ CutoffDiagonal

theorem drop_quotient (M N : ℕ) (h : N≤M) (p : A ℝ Bool) :
    drop M N h (TruncatedWords.quotient ∅ M p)=TruncatedWords.quotient ∅ N p := by
  have he : (drop M N h).comp (TruncatedWords.quotient ∅ M)=TruncatedWords.quotient ∅ N := by
    apply AssociativeElimination.hom_ext
    intro a
    exact drop_gen M N h a
  exact AlgHom.congr_fun he p

end CutoffPrimitiveExtract

namespace OperatorLog
open Polynomial
variable {V : Type*} [AddCommGroup V] [Module ℚ V]
variable (N : ℕ) (T : Module.End ℚ V) (hT : T^(N+1)=0)

 include hT
 theorem value_taylor (a : V) (l : V →ₗ[ℚ] ℚ) (m : ℕ) :
    taylor (m:ℚ) (valuePolynomial N T a l)=valuePolynomial N T (((1+T)^m) a) l := by
  apply polynomial_ext_nat
  intro n
  rw [taylor_eval,←Nat.cast_add,value_eval,interpolate_nat N T hT,value_eval,
    interpolate_nat N T hT,pow_add,Module.End.mul_apply]

 theorem value_derivative (a : V) (l : V →ₗ[ℚ] ℚ) :
    (valuePolynomial N T a l).derivative=valuePolynomial N T a (l.comp (logarithm N T)) := by
  apply polynomial_ext_nat
  intro m
  rw [←taylor_coeff_one,value_taylor N T hT,value_one,value_eval,interpolate_nat N T hT]
  rfl

 theorem value_zero (a : V) (l : V →ₗ[ℚ] ℚ) : (valuePolynomial N T a l).coeff 0=l a := by
  rw [coeff_zero_eq_eval_zero,value_eval]
  have h := interpolate_nat N T hT 0
  simpa only [Nat.cast_zero,pow_zero,Module.End.one_apply] using congrArg (fun f : Module.End ℚ V => l (f a)) h

 theorem value_coeff (a : V) (l : V →ₗ[ℚ] ℚ) (k : ℕ) :
    (valuePolynomial N T a l).coeff k=(k.factorial:ℚ)⁻¹*l (((logarithm N T)^k) a) := by
  induction k generalizing l with
  | zero => simp only [value_zero N T hT,Nat.factorial_zero,Nat.cast_one,inv_one,pow_zero,Module.End.one_apply,one_mul]
  | succ k ih =>
    have hh := congrArg (fun p : ℚ[X] => p.coeff k) (value_derivative N T hT a l)
    rw [coeff_derivative,ih] at hh
    have hk : (k+1:ℚ)≠0 := by positivity
    rw [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    rw [pow_succ',Module.End.mul_apply]
    change _= _*l (logarithm N T (((logarithm N T)^k) a))
    change (valuePolynomial N T a l).coeff (k+1)*(↑k+1:ℚ)=
      (↑k.factorial:ℚ)⁻¹*l (logarithm N T (((logarithm N T)^k) a)) at hh
    have hf : (k.factorial:ℚ)≠0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    field_simp at hh ⊢
    nlinarith [hh]

 theorem exp_logarithm (hL : IsNilpotent (logarithm N T)) :
    IsNilpotent.exp (logarithm N T)=1+T := by
  apply LinearMap.ext
  intro a
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff ℚ _).mp
  intro l
  rw [map_sub]
  obtain ⟨m,hm⟩ := hL
  let M := m+(valuePolynomial N T a l).natDegree+1
  have hmM : (logarithm N T)^M=0 := pow_eq_zero_of_le (by dsimp [M]; omega) hm
  rw [IsNilpotent.exp_eq_sum hmM,LinearMap.sum_apply,map_sum]
  have hp := (valuePolynomial N T a l).eval_eq_sum_range' (n:=M) (by dsimp [M]; omega) (1:ℚ)
  simp only [one_pow,mul_one,value_coeff N T hT] at hp
  have hi : interpolate N T 1=1+T := by simpa only [Nat.cast_one,pow_one] using interpolate_nat N T hT 1
  rw [value_eval,hi] at hp
  simp only [LinearMap.smul_apply,map_smul,smul_eq_mul,hp,sub_self]
end OperatorLog

namespace CategoryExp

section
open IsNilpotent
variable {R A B O P : Type*} [CommRing R] [Ring A] [Algebra R A] [Module ℚ A]
  [Ring B] [Algebra R B] [Module ℚ B]

 omit [Module ℚ A] in
 theorem pow_mem {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1))
    (i n : ℕ) {a : A} (ha : a∈F.step n) : (d^i) a∈F.step (n+i) := by
  induction i with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.add_zero] using ha
  | succ i ih =>
    rw [_root_.pow_succ',Module.End.mul_apply]
    simpa only [Nat.add_assoc] using hd (n+i) _ ih

 omit [Module ℚ A] in
 theorem nilpotent {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (d : Module.End R A) (hd : ∀ n a,a∈F.step n → d a∈F.step (n+1)) : IsNilpotent d := by
  refine ⟨N+1,LinearMap.ext (fun a => ?_)⟩
  have hh := pow_mem F d hd (N+1) 0 (a:=a) (by rw [F.initial]; trivial)
  simpa only [Nat.zero_add,F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hh

end

open IsNilpotent
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V]
  [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]
variable {N : ℕ} (F : FilteredComparison.Filtration R V N)
  (d : Module.End R V) (k : ℕ)
  (hd : ∀ n a,a∈F.step n → d a∈F.step (n+k))

include hd
omit [Algebra ℚ R] [Module ℚ V] [IsScalarTower ℚ R V] in
 theorem pow_mem_shift (i n : ℕ) {a : V} (ha : a∈F.step n) : (d^i) a∈F.step (n+i*k) := by
  induction i with
  | zero => simpa only [pow_zero,Module.End.one_apply,Nat.zero_mul,Nat.add_zero] using ha
  | succ i ih =>
    rw [_root_.pow_succ',Module.End.mul_apply]
    simpa only [Nat.succ_mul,Nat.add_assoc] using hd (n+i*k) _ ih

 theorem first_order (hk : 0<k) (n : ℕ) {a : V} (ha : a∈F.step n) :
    exp d a-a-d a∈F.step (n+2*k) := by
  have hn : IsNilpotent d := by
    refine ⟨N+1,LinearMap.ext (fun a => ?_)⟩
    have hp := pow_mem_shift F d k hd (N+1) 0 (a:=a) (by rw [F.initial]; trivial)
    have hp' := F.decreasing (show N+1≤0+(N+1)*k by simpa using Nat.le_mul_of_pos_right (N+1) hk) hp
    simpa only [F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hp'
  obtain ⟨s,hs⟩ := hn
  have hs' : d^(2+s)=0 := pow_eq_zero_of_le (by omega) hs
  rw [exp_eq_sum hs',LinearMap.sum_apply,Finset.sum_range_add]
  have htwo : (∑ i∈Finset.range 2,((↑i.factorial : ℚ)⁻¹ • d^i) a)=a+d a := by
    simp [Finset.sum_range_succ]
  rw [htwo]
  have hsum : (∑ i∈Finset.range s,((↑(2+i).factorial : ℚ)⁻¹ • d^(2+i)) a)∈F.step (n+2*k) := by
    apply Submodule.sum_mem
    intro i hi
    change (↑(2+i).factorial : ℚ)⁻¹ • (d^(2+i)) a∈_
    apply ((F.step (n+2*k)).restrictScalars ℚ).smul_mem
    apply F.decreasing _ (pow_mem_shift F d k hd (2+i) n ha)
    exact Nat.add_le_add_left (Nat.mul_le_mul_right k (by omega)) n
  convert hsum using 1; abel

 theorem unit_leading (hk : 0<k) {a u : V} (_hu : u∈F.step 0) (ha : a-u∈F.step 1) :
    exp d a-a-d u∈F.step (k+1) := by
  have ha0 : a∈F.step 0 := by rw [F.initial]; trivial
  have h₁ := first_order F d k hd hk 0 ha0
  have h₂ := hd 1 (a-u) ha
  rw [map_sub] at h₂
  have h₁' : exp d a-a-d a∈F.step (k+1) := F.decreasing (by omega) h₁
  have h₂' : d a-d u∈F.step (k+1) := by simpa only [Nat.add_comm 1 k] using h₂
  convert (F.step (k+1)).add_mem h₁' h₂' using 1; abel

end CategoryExp

namespace RealOperatorLog
variable {V : Type*} [AddCommGroup V] [Module ℝ V] [Module ℚ V] [IsScalarTower ℚ ℝ V]
 def logarithm (N : ℕ) (T : Module.End ℝ V) : Module.End ℝ V :=
  ∑ k∈Finset.range N,((-1:ℚ)^k/(k+1)) • T^(k+1)
 theorem pow_restrict (T : Module.End ℝ V) (k : ℕ) (a : V) :
    ((T.restrictScalars ℚ)^k) a=(T^k) a := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [pow_succ',Module.End.mul_apply,ih]; rfl
 theorem restrict (N : ℕ) (T : Module.End ℝ V) :
    (logarithm N T).restrictScalars ℚ=OperatorLog.logarithm N (T.restrictScalars ℚ) := by
  apply LinearMap.ext
  intro a
  change logarithm N T a=OperatorLog.logarithm N (T.restrictScalars ℚ) a
  simp only [OperatorLog.logarithm_eq,logarithm,LinearMap.sum_apply,LinearMap.smul_apply,pow_restrict]
 theorem raises {M : ℕ} (F : FilteredComparison.Filtration ℝ V M)
    (N : ℕ) (T : Module.End ℝ V) (hT : ∀ m a,a∈F.step m → T a∈F.step (m+1))
    (m : ℕ) (a : V) (ha : a∈F.step m) : logarithm N T a∈F.step (m+1) := by
  rw [logarithm,LinearMap.sum_apply]
  apply Submodule.sum_mem
  intro k hk
  change ((-1:ℚ)^k/(k+1)) • (T^(k+1)) a∈_
  apply ((F.step (m+1)).restrictScalars ℚ).smul_mem
  have hp := CategoryExp.pow_mem_shift F T 1 hT (k+1) m ha
  simp only [Nat.mul_one] at hp
  exact F.decreasing (by omega) hp
 theorem exp_restrict (T : Module.End ℝ V) (hT : IsNilpotent T) (a : V) :
    IsNilpotent.exp (T.restrictScalars ℚ) a=IsNilpotent.exp T a := by
  obtain ⟨k,hk⟩ := hT
  have hkr : (T.restrictScalars ℚ)^k=0 := by
    apply LinearMap.ext
    intro u
    rw [pow_restrict,hk]
    rfl
  rw [IsNilpotent.exp_eq_sum hk,IsNilpotent.exp_eq_sum hkr,LinearMap.sum_apply,LinearMap.sum_apply]
  simp only [LinearMap.smul_apply,pow_restrict]
 theorem exp_logarithm (N : ℕ) (T : Module.End ℝ V) (hT : T^(N+1)=0)
    (hL : IsNilpotent (logarithm N T)) : IsNilpotent.exp (logarithm N T)=1+T := by
  have hTr : (T.restrictScalars ℚ)^(N+1)=0 := by
    apply LinearMap.ext
    intro a
    rw [pow_restrict,hT]
    rfl
  have hLr : IsNilpotent (OperatorLog.logarithm N (T.restrictScalars ℚ)) := by
    rw [←restrict]
    obtain ⟨k,hk⟩ := hL
    refine ⟨k,LinearMap.ext (fun a => ?_)⟩
    rw [pow_restrict,hk]
    rfl
  apply LinearMap.ext
  intro a
  rw [←exp_restrict _ hL,restrict,OperatorLog.exp_logarithm N _ hTr hLr]
  rfl
end RealOperatorLog

namespace TruncatedDerivation
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R]
variable (P : Set (A R α)) (N : ℕ)
local notation "Q" => TruncatedWords.Q P N
local notation "F" => filtration P N

 theorem derivation_mem (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈F (k+1))
    (hP : ∀ p∈P,raw P N v p=0) {n : ℕ} {p : Q} (hp : p∈F n) :
    derivation P N k v hv hP p∈F (n+k) := by
  obtain ⟨p,hp,rfl⟩ := hp
  change derivation P N k v hv hP (quotient P N p)∈_
  rw [derivation_quotient]
  exact raw_mem P N k v hv hp

end TruncatedDerivation

namespace CutoffCategory
open AssociativeElimination WordGrading TruncatedWords
variable {α O : Type*} (P : Set (A ℝ α)) (N : ℕ)

 theorem initial : (TruncatedWords.filtration P N) 0=⊤ := by
  apply top_unique
  intro a _
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations P N) a
  exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩

 def filtration : FilteredComparison.Filtration ℝ (TruncatedWords.Q P N) N where
  step := (TruncatedWords.filtration P N)
  decreasing := filtration_antitone P N
  initial := initial P N
  terminal := filtration_terminal P N

 variable (d : Module.End ℝ (TruncatedWords.Q P N)) (hd : ∀ a b,d (a*b)=d a*b+a*d b) (h1 : d 1=0)
  (h : O → (TruncatedWords.Q P N))

 abbrev data : CategoryExp.Data ℝ (TruncatedWords.Q P N) O := CategoryExp.gauge d hd h1 h

 theorem apply (p q : O) (a : (TruncatedWords.Q P N)) : (data P N d hd h1 h).D p q a=d a+h q*a-a*h p := rfl

 theorem raises (k : ℕ) (hdF : ∀ n a,a∈(TruncatedWords.filtration P N) n → d a∈(TruncatedWords.filtration P N) (n+k)) (hhF : ∀ p,h p∈(TruncatedWords.filtration P N) k)
    (p q : O) (n : ℕ) (a : (TruncatedWords.Q P N)) (ha : a∈(TruncatedWords.filtration P N) n) : (data P N d hd h1 h).D p q a∈(TruncatedWords.filtration P N) (n+k) := by
  rw [apply]
  apply Submodule.sub_mem
  · apply Submodule.add_mem
    · exact hdF n a ha
    · simpa only [Nat.add_comm k n] using filtration_mul P N k n (hhF q) ha
  · exact filtration_mul P N n k ha (hhF p)

end CutoffCategory

namespace KZRealLog
open KZComparison CutoffDepth CutoffKZ
 def S (N : ℕ) (p q : Bool) : Module.End ℝ (Q ℝ N) :=
  ((LinearMap.mulLeft ℝ (frames N q:Q ℝ N)).comp (LinearMap.mulRight ℝ ((frames N p)⁻¹:(Q ℝ N)ˣ))).comp (theta N).toLinearMap
 theorem S_apply (N : ℕ) (p q : Bool) (a : Q ℝ N) :
    S N p q a=(frames N q:Q ℝ N)*theta N a*((frames N p)⁻¹:(Q ℝ N)ˣ) := by
  simp only [S,LinearMap.comp_apply,LinearMap.mulLeft_apply,LinearMap.mulRight_apply,mul_assoc]
  rfl
 theorem S_restrict (N : ℕ) (p q : Bool) : (S N p q).restrictScalars ℚ=(category N).S p q := by
  apply LinearMap.ext
  intro a
  rw [show (S N p q).restrictScalars ℚ a=S N p q a from rfl,S_apply]
  simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,AlgEquiv.restrictScalars_apply]
 def D (N : ℕ) (p q : Bool) : Module.End ℝ (Q ℝ N) :=
  RealOperatorLog.logarithm (N+1) (S N p q-1)
 theorem D_restrict (N : ℕ) (p q : Bool) :
    (D N p q).restrictScalars ℚ=LogCategory.delta (category N) p q := by
  rw [D,RealOperatorLog.restrict]
  have hh : (S N p q-1).restrictScalars ℚ=(category N).S p q-1 := by
    apply LinearMap.ext
    intro a
    change S N p q a-a=(category N).S p q a-a
    rw [←S_restrict]
    rfl
  rw [hh]
  rfl
 theorem D_apply (N : ℕ) (p q : Bool) (a : Q ℝ N) :
    D N p q a=LogCategory.delta (category N) p q a :=
  LinearMap.congr_fun (D_restrict N p q) a
 def data (N : ℕ) : CategoryExp.Data ℝ (Q ℝ N) Bool where
  D := D N
  comp p q r a b := by simp only [D_apply]; exact LogCategory.delta_comp _ p q r a b
  one p := by rw [D_apply,LogCategory.delta_one_loop]
 theorem value (N : ℕ) : D N false true 1=KZComparison.value N := D_apply N false true 1
 theorem frames_weight (N : ℕ) (p : Bool) :
    (frames N p:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1 := by
  cases p
  · simp [frames]
  · exact ConjugateComparison.unitArrow_normalized N _ _ _ _
 theorem S_raises (N : ℕ) (p q : Bool) (m : ℕ) (a : Q ℝ N)
    (ha : a∈TruncatedWords.filtration ∅ N m) : S N p q a-a∈TruncatedWords.filtration ∅ N (m+1) := by
  have h0 : ((TruncatedWords.filtration (∅:Set (AssociativeElimination.A ℝ Bool)) N 0).restrictScalars ℚ)=⊤ := by
    rw [CutoffCategory.initial]
    rfl
  exact GaugeAutomorphism.raises ((theta N).restrictScalars ℚ) (frames N)
    (fun m => (TruncatedWords.filtration ∅ N m).restrictScalars ℚ)
    (TruncatedWords.filtration_antitone ∅ N) h0 (TruncatedWords.filtration_mul ∅ N)
    (ConjugateComparison.theta_raises N _ _ _ _) (frames_weight N) p q m a ha
 theorem raises (N : ℕ) (p q : Bool) (m : ℕ) (a : Q ℝ N)
    (ha : a∈TruncatedWords.filtration ∅ N m) : D N p q a∈TruncatedWords.filtration ∅ N (m+1) :=
  RealOperatorLog.raises (CutoffCategory.filtration ∅ N) (N+1) (S N p q-1) (S_raises N p q) m a ha
 theorem nilpotent (N : ℕ) (p q : Bool) : IsNilpotent (D N p q) :=
  CategoryExp.nilpotent (CutoffCategory.filtration ∅ N) (D N p q) (raises N p q)
 theorem exp_eq (N : ℕ) (p q : Bool) : IsNilpotent.exp (D N p q)=S N p q := by
  have hn : (S N p q-1)^(N+1+1)=0 := by
    apply LinearMap.ext
    intro a
    have h := LinearMap.congr_fun ((category N).nilpotent p q) a
    have hr : (S N p q-1).restrictScalars ℚ=(category N).S p q-1 := by
      apply LinearMap.ext
      intro a
      change S N p q a-a=(category N).S p q a-a
      rw [←S_restrict]
      rfl
    rw [←hr,RealOperatorLog.pow_restrict] at h
    exact h
  rw [D,RealOperatorLog.exp_logarithm (N+1) _ hn (nilpotent N p q)]
  abel
 theorem exp_comparison (N : ℕ) :
    IsNilpotent.exp (D N false true) (positive N:Q ℝ N)=(negative N:Q ℝ N) := by
  rw [exp_eq,S_apply]
  simpa only [frames,inv_one,Units.val_one,mul_one] using exact_comparison N
 theorem loop_x (N : ℕ) : D N false false (X N)=0 := by
  rw [D_apply]
  apply OperatorLog.logarithm_fixed
  change (category N).S false false (X N)-X N=0
  rw [←S_restrict]
  change S N false false (X N)-X N=0
  simp only [S_apply,frames,Units.val_one,inv_one,mul_one,one_mul,theta_x,sub_self]
 theorem loop_y (N : ℕ) : D N true true (Y N)=0 := by
  rw [D_apply]
  apply OperatorLog.logarithm_fixed
  change (category N).S true true (Y N)-Y N=0
  rw [←S_restrict]
  change S N true true (Y N)-Y N=0
  simp only [S_apply,frames,theta_y,mul_assoc,Units.mul_inv_cancel_left,Units.mul_inv,mul_one,sub_self]
 theorem loop_false_y (N : ℕ) :
    D N false false (Y N)=Y N*KZComparison.value N-KZComparison.value N*Y N := by
  have hh := LogCategory.delta_formula (category N) false true true (Y N)
  rw [←D_apply,loop_y] at hh
  rw [←D_apply N false false] at hh
  change 0=D N false false (Y N)+KZComparison.value N*Y N-Y N*KZComparison.value N at hh
  apply eq_sub_iff_add_eq.mpr
  have hh' : D N false false (Y N)+KZComparison.value N*Y N=Y N*KZComparison.value N := sub_eq_zero.mp hh.symm
  exact hh'
 theorem edge_formula (N : ℕ) (a : Q ℝ N) :
    D N false true a=D N false false a+KZComparison.value N*a := by
  rw [D_apply,LogCategory.delta_formula (category N) false,LogCategory.delta_one_loop,mul_zero,sub_zero,←D_apply]
  rfl
end KZRealLog

end DeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section
namespace RealDeligneDrinfeld

theorem t_disjoint (i j k l : Fin 4)
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) :
    ⁅t i j,t k l⁆ = 0 := by
  rw [t, t, ← LieSubmodule.Quotient.mk_bracket, LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inl ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩)

theorem t_three (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    ⁅t i j,t i k + t j k⁆ = 0 := by
  change LieSubmodule.Quotient.mk (⁅chord i j, chord i k + chord j k⁆) = (0 : T4)
  rw [LieSubmodule.Quotient.mk_eq_zero']
  exact LieSubmodule.subset_lieSpan (Or.inr ⟨i,j,k,hij,hik,hjk,rfl⟩)

namespace T4Universal
variable {M : Type*} [LieRing M] [LieAlgebra ℝ M]

def pre (f : Fin 4 → Fin 4 → M) : BraidFree →ₗ⁅ℝ⁆ M :=
  FreeLieAlgebra.lift ℝ (fun e => f e.val.1 e.val.2)

theorem pre_chord (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0) (i j : Fin 4) :
    pre f (chord i j) = f i j := by
  unfold chord
  split_ifs with hij hji
  · simp [pre]
  · simp [pre, hs j i]
  · have h : i = j := le_antisymm (le_of_not_gt hji) (le_of_not_gt hij)
    subst j
    simp [hz]

def lift (f : Fin 4 → Fin 4 → M)
    (hs : ∀ i j, f i j = f j i) (hz : ∀ i, f i i = 0)
    (hd : ∀ i j k l, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ⁅f i j,f k l⁆ = 0)
    (ht : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ⁅f i j,f i k+f j k⁆ = 0) : T4 →ₗ⁅ℝ⁆ M := by
  have hker : braidIdeal ≤ (pre f).ker := by
    rw [braidIdeal, LieSubmodule.lieSpan_le]
    intro z hz'
    change pre f z = 0
    rcases hz' with ⟨i,j,k,l,hij,hik,hil,hjk,hjl,hkl,rfl⟩ | ⟨i,j,k,hij,hik,hjk,rfl⟩
    · simpa only [LieHom.map_lie, pre_chord f hs hz] using hd i j k l hij hik hil hjk hjl hkl
    · simpa only [LieHom.map_lie, map_add, pre_chord f hs hz] using ht i j k hij hik hjk
  exact { braidIdeal.toSubmodule.liftQ (pre f).toLinearMap hker with
    map_lie' := by
      intro a b
      induction a using Submodule.Quotient.induction_on with | _ a =>
        induction b using Submodule.Quotient.induction_on with | _ b =>
          exact (pre f).map_lie a b }

@[simp] theorem lift_t (f : Fin 4 → Fin 4 → M) (hs hz hd ht) (i j : Fin 4) :
    lift f hs hz hd ht (t i j) = f i j := pre_chord f hs hz i j

end T4Universal

end RealDeligneDrinfeld

end

end OAI

end

section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.WeightBridge
open DeligneDrinfeld.LieGrading DeligneDrinfeld.UniversalEmbedding
variable {α : Type*}

 theorem bracket_mem {wt : α → ℕ} {n m : ℕ} {a b : FreeLieAlgebra ℝ α}
    (ha : a∈weightPiece wt n) (hb : b∈weightPiece wt m) : ⁅a,b⁆∈weightPiece wt (n+m) := by
  apply Submodule.span_induction (p:=fun a _ => ⁅a,b⁆∈weightPiece wt (n+m)) ?_ ?_ ?_ ?_ ha
  · intro a ha
    apply Submodule.span_induction (p:=fun b _ => ⁅a,b⁆∈weightPiece wt (n+m)) ?_ ?_ ?_ ?_ hb
    · intro b hb; exact Submodule.subset_span (WeightedWord.bracket ha hb)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro s b _ hb; rw [lie_smul]; exact Submodule.smul_mem _ s hb
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_lie]; exact Submodule.add_mem _ ha hb
  · intro s a _ ha; rw [smul_lie]; exact Submodule.smul_mem _ s ha

 theorem map_mem {β : Type*} (f : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ FreeLieAlgebra ℝ β)
    (wa : α → ℕ) (wb : β → ℕ) (hf : ∀ a,f (FreeLieAlgebra.of ℝ a)∈weightPiece wb (wa a))
    {n : ℕ} {p : FreeLieAlgebra ℝ α} (hp : p∈weightPiece wa n) : f p∈weightPiece wb n := by
  have hw : ∀ n p,WeightedWord wa n p → f p∈weightPiece wb n := by
    intro n p hp
    induction hp with
    | generator a => exact hf a
    | bracket hp hq ihp ihq => rw [LieHom.map_lie]; exact bracket_mem ihp ihq
  apply Submodule.span_induction (p:=fun p _ => f p∈weightPiece wb n) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact hw n p hp
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro p q _ _ hp hq; rw [map_add]; exact Submodule.add_mem _ hp hq
  · intro s p _ hp; rw [map_smul]; exact Submodule.smul_mem _ s hp

 theorem eval_mem {n : ℕ} {p : L} (hp : p∈Ln n) {a b : L} (ha : a∈Ln 1) (hb : b∈Ln 1) :
    eval a b p∈Ln n := by
  apply map_mem (eval a b) (fun _ => 1) (fun _ => 1) (fun i => ?_) hp
  cases i <;> simpa [eval] using (by assumption : _∈Ln 1)

 theorem x_mem : x∈Ln 1 := Submodule.subset_span (WeightedWord.generator _)

end RealDeligneDrinfeld.WeightBridge

namespace DeligneDrinfeld.UnitConjugation
variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

def hom (u : Aˣ) : A →ₐ[R] A where
  toFun a := (u:A)*a*((u⁻¹:Aˣ):A)
  map_zero' := by simp only [mul_zero,zero_mul]
  map_one' := by simp only [mul_one,Units.mul_inv]
  map_add' a b := by rw [mul_add,add_mul]
  map_mul' a b := by
    simp only [mul_assoc]
    rw [←mul_assoc (((u⁻¹:Aˣ):A)) (u:A),Units.inv_mul,one_mul]
  commutes' r := by
    rw [←Algebra.commutes,mul_assoc,Units.mul_inv,mul_one]

@[simp] theorem hom_apply (u : Aˣ) (a : A) : hom (R:=R) u a=(u:A)*a*((u⁻¹:Aˣ):A) := rfl

@[simp] theorem inverse (u : Aˣ) (a : A) : hom (R:=R) u⁻¹ (hom (R:=R) u a)=a := by
  simp only [hom_apply,inv_inv,mul_assoc]
  rw [Units.inv_mul_cancel_left,Units.inv_mul,mul_one]

@[simp] theorem mul_apply (u v : Aˣ) (a : A) : hom (R:=R) (u*v) a=hom (R:=R) u (hom (R:=R) v a) := by
  simp only [hom_apply,Units.val_mul,mul_inv_rev,mul_assoc]

theorem natural {B : Type*} [Ring B] [Algebra R B] (f : A →ₐ[R] B) (u : Aˣ) (a : A) :
    f (hom (R:=R) u a)=hom (R:=R) (Units.map f.toMonoidHom u) (f a) := by
  simp only [hom_apply,map_mul]
  rfl

end DeligneDrinfeld.UnitConjugation

namespace DeligneDrinfeld.KZCollar
open FinitePicard
variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]

theorem associator_swap (F : NilpotentFiltration A) {X Y : A}
    (hX : X∈F.space 1) (hY : Y∈F.space 1) :
    associator F Y X=Ring.inverse (associator F X Y) := by
  unfold associator rightSolution
  norm_num only [show (1:ℝ)-1/2=1/2 by norm_num]
  rw [Ring.inverse_mul (Or.inr (normalizedSolution_isUnit F hX hY (1/2))),
    Ring.inverse_inverse (normalizedSolution_isUnit F hY hX (1/2))]

end DeligneDrinfeld.KZCollar

namespace DeligneDrinfeld.KZSwap

section
open CutoffDepth CutoffKZ KZComparison

def swap (N : ℕ) : Q ℝ N →ₐ[ℝ] Q ℝ N :=
  NilpotentFreeLift.eval (weight N) (fun b => gen N (!b)) (fun b => gen_weight N (!b))
@[simp] theorem swap_gen (N : ℕ) (b : Bool) : swap N (gen N b)=gen N (!b) :=
  NilpotentFreeLift.eval_gen _ _ _ b

theorem positive_swap (N : ℕ) : Units.map (swap N).toMonoidHom (positive N)=(positive N)⁻¹ := by
  apply Units.ext
  change swap N (positive N:Q ℝ N)=((positive N)⁻¹:(Q ℝ N)ˣ)
  rw [positive_val,KZCollar.map_associator (swap N) (weight N) (weight N) rfl
    (gen_weight N false) (gen_weight N true),swap_gen,swap_gen]
  simp only [Bool.not_false, Bool.not_true]
  rw [KZCollar.associator_swap (weight N) (gen_weight N false) (gen_weight N true),
    ←positive_val,Ring.inverse_unit]

theorem negative_swap (N : ℕ) : Units.map (swap N).toMonoidHom (negative N)=(negative N)⁻¹ := by
  apply Units.ext
  change swap N (negative N:Q ℝ N)=((negative N)⁻¹:(Q ℝ N)ˣ)
  rw [negative_val,KZCollar.map_associator (swap N) (weight N) (weight N) rfl
    ((weight N).space 1|>.neg_mem (gen_weight N false))
    ((weight N).space 1|>.neg_mem (gen_weight N true)),map_neg,map_neg,swap_gen,swap_gen]
  simp only [Bool.not_false, Bool.not_true]
  rw [KZCollar.associator_swap (weight N)
    ((weight N).space 1|>.neg_mem (gen_weight N false))
    ((weight N).space 1|>.neg_mem (gen_weight N true)),←negative_val,Ring.inverse_unit]

open ConjugateComparison
 theorem transport_swap (N : ℕ) (P : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hdual : Units.map (swap N).toMonoidHom P=P⁻¹) (u : Q ℝ N) :
    swap N (transport N P hP u)=UnitConjugation.hom (R := ℝ) P (transport N P hP (swap N u)) := by
  have hd : swap N (P:Q ℝ N)=((P⁻¹:(Q ℝ N)ˣ):Q ℝ N) := congrArg Units.val hdual
  have hi : swap N ((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)=(P:Q ℝ N) := by
    have hh := congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) hdual
    rw [←map_inv] at hh
    change swap N (((P⁻¹:(Q ℝ N)ˣ):Q ℝ N))=(((P⁻¹)⁻¹:(Q ℝ N)ˣ):Q ℝ N) at hh
    simpa only [inv_inv] using hh
  have he : (swap N).comp (transport N P hP).toAlgHom=
      (UnitConjugation.hom (R := ℝ) P).comp ((transport N P hP).toAlgHom.comp (swap N)) := by
    apply TruncatedSubstitution.hom_ext N
    intro b
    change swap N (transport N P hP (gen N b))=
      UnitConjugation.hom (R := ℝ) P (transport N P hP (swap N (gen N b)))
    rw [ConjugateCoalgebra.transport_cutoff_gen,swap_gen,ConjugateCoalgebra.transport_cutoff_gen]
    cases b
    · change swap N (gen N false)=(P:Q ℝ N)*
        (((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)*gen N true*(P:Q ℝ N))*((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)
      rw [swap_gen]
      simp only [mul_assoc,Units.mul_inv_cancel_left,Units.mul_inv,mul_one,Bool.not_false]
    · change swap N (((P⁻¹:(Q ℝ N)ˣ):Q ℝ N)*gen N true*(P:Q ℝ N))=_
      rw [map_mul,map_mul,hi,hd,swap_gen]
      rfl
  exact AlgHom.congr_fun he u

 theorem theta_swap (N : ℕ) (P V : (Q ℝ N)ˣ)
    (hP : (P:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hV : (V:Q ℝ N)-1∈TruncatedWords.filtration ∅ N 1)
    (hdP : Units.map (swap N).toMonoidHom P=P⁻¹)
    (hdV : Units.map (swap N).toMonoidHom V=V⁻¹) (u : Q ℝ N) :
    swap N (ConjugateComparison.theta N P V hP hV u)=
      UnitConjugation.hom (R := ℝ) (unitArrow N P V hP hV)
        (ConjugateComparison.theta N P V hP hV (swap N u)) := by
  obtain ⟨v,rfl⟩ := (transport N P hP).surjective u
  rw [theta_transport,transport_swap N V hV hdV,transport_swap N P hP hdP]
  rw [show ConjugateComparison.theta N P V hP hV
      (UnitConjugation.hom (R:=ℝ) P (transport N P hP (swap N v))) =
      UnitConjugation.hom (R:=ℝ) (Units.map (ConjugateComparison.theta N P V hP hV).toMonoidHom P)
      (ConjugateComparison.theta N P V hP hV (transport N P hP (swap N v))) from
      UnitConjugation.natural (ConjugateComparison.theta N P V hP hV).toAlgHom P _]
  rw [theta_transport,←UnitConjugation.mul_apply]
  have he : unitArrow N P V hP hV*Units.map (ConjugateComparison.theta N P V hP hV).toMonoidHom P=V := by
    unfold unitArrow
    group
  rw [he]

 theorem arrow_swap (N : ℕ) : Units.map (swap N).toMonoidHom (arrow N)=(arrow N)⁻¹ := by
  let P := positive N
  let V := negative N
  let U := arrow N
  let θ := KZComparison.theta N
  have hθ : Units.map (swap N).toMonoidHom (Units.map θ.toMonoidHom P)=
      U*Units.map θ.toMonoidHom (Units.map (swap N).toMonoidHom P)*U⁻¹ := by
    apply Units.ext
    exact theta_swap N P V (positive_weight N) (negative_weight N)
      (positive_swap N) (negative_swap N) (P:Q ℝ N)
  have he : Units.map (swap N).toMonoidHom U=
      V⁻¹*(U*(Units.map θ.toMonoidHom P)⁻¹*U⁻¹)⁻¹ := by
    change Units.map (swap N).toMonoidHom
      (V*(Units.map θ.toMonoidHom P)⁻¹)=_
    rw [map_mul,map_inv,negative_swap,hθ,positive_swap,map_inv]
  rw [he]
  change V⁻¹*((V*(Units.map θ.toMonoidHom P)⁻¹)*(Units.map θ.toMonoidHom P)⁻¹*
    (V*(Units.map θ.toMonoidHom P)⁻¹)⁻¹)⁻¹=(V*(Units.map θ.toMonoidHom P)⁻¹)⁻¹
  group

end

open CutoffDepth CutoffKZ KZComparison

 theorem category_swap (N : ℕ) (p q : Bool) (u : Q ℝ N) :
    swap N ((category N).S p q u)=(category N).S (!p) (!q) (swap N u) := by
  have hθ := theta_swap N (positive N) (negative N) (positive_weight N) (negative_weight N)
    (positive_swap N) (negative_swap N) u
  change swap N (theta N u)=(arrow N:Q ℝ N)*theta N (swap N u)*((arrow N)⁻¹:(Q ℝ N)ˣ) at hθ
  have hU : swap N (arrow N:Q ℝ N)=((arrow N)⁻¹:(Q ℝ N)ˣ) := congrArg Units.val (arrow_swap N)
  have hI : swap N (((arrow N)⁻¹:(Q ℝ N)ˣ):Q ℝ N)=(arrow N:Q ℝ N) := by
    have h := congrArg (fun v => ((v⁻¹:(Q ℝ N)ˣ):Q ℝ N)) (arrow_swap N)
    rw [←map_inv] at h
    change swap N (((arrow N)⁻¹:(Q ℝ N)ˣ):Q ℝ N)=_ at h
    simpa only [inv_inv] using h
  cases p <;> cases q <;>
    simp only [category,GaugeAutomorphism.data,GaugeAutomorphism.map_apply,AlgEquiv.restrictScalars_apply,frames,
      Bool.not_false,Bool.not_true,Units.val_one,inv_one,mul_one,one_mul,map_mul,
      hθ,hU,hI,mul_assoc,Units.inv_mul_cancel_left,Units.inv_mul,mul_one]

 theorem value_swap (N : ℕ) : swap N (value N)= -value N := by
  have h := OperatorLog.logarithm_natural (category N).N
    ((category N).S false true-1) ((category N).S true false-1)
    ((swap N).toLinearMap.restrictScalars ℚ) (by
      intro u
      change swap N ((category N).S false true u-u)=(category N).S true false (swap N u)-swap N u
      rw [map_sub,category_swap]
      rfl) (1:Q ℝ N)
  change swap N (value N)=LogCategory.delta (category N) true false (swap N 1) at h
  rw [map_one] at h
  have hh := LogCategory.unit_cocycle (category N) false true false
  rw [LogCategory.delta_one_loop] at hh
  exact h.trans (eq_neg_of_add_eq_zero_left hh.symm)

end DeligneDrinfeld.KZSwap

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace DeligneDrinfeld
end DeligneDrinfeld

end

end OAI

end


section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.KZHomogeneous
open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
abbrev V (N : ℕ) : A ℝ Bool := normalVal N (KZComparison.value N)
def q (n : ℕ) : L := if h:0<n then (KZ_value_lie n n h le_rfl).choose else 0
 theorem q_homogeneous (n : ℕ) : q n∈Ln n := by
  unfold q
  split_ifs with h
  · rw [Ln,WeightBridge.piece_eq]
    exact (KZ_value_lie n n h le_rfl).choose_spec.1
  · exact Submodule.zero_mem _
 theorem q_embed (n : ℕ) (hn : 0<n) : embed (q n)=TensorProjection.piece n (V n) := by
  simp only [q,dif_pos hn]
  exact (KZ_value_lie n n hn le_rfl).choose_spec.2
 theorem normal_mem {N k : ℕ} {u : CutoffDepth.Q ℝ N} (hu : u∈filtration ∅ N k) :
    normalVal N u∈above (fun _ => 1) k := by
  obtain ⟨p,hp,rfl⟩ := hu
  change normalVal N (quotient ∅ N p)∈_
  rw [normalVal_quotient]
  exact project_preserves hp
 theorem quotient_normal (N : ℕ) (u : CutoffDepth.Q ℝ N) : quotient ∅ N (normalVal N u)=u := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations (∅:Set (A ℝ Bool)) N) u
  change quotient ∅ N (normalVal N (quotient ∅ N p))=quotient ∅ N p
  rw [normalVal_quotient]
  have hh := quotient_above (∅:Set (A ℝ Bool)) N (TruncatedFree.sub_trunc_above N p)
  rw [map_sub] at hh
  exact (sub_eq_zero.mp hh).symm
 theorem value_above (N : ℕ) : V N∈above (fun _ => 1) 1 := by
  apply normal_mem
  rw [←KZRealLog.value]
  exact KZRealLog.raises N false true 0 1 (filtration_one ∅ N)
 theorem q_embed_zero : embed (q 0)=TensorProjection.piece 0 (V 0) := by
  change (0:A ℝ Bool)=TensorProjection.piece 0 (V 0)
  symm
  exact project_eq_zero (value_above 0) (by intro w hw hh; change 1≤degree (fun _ => 1) w at hw; omega)
 theorem piece_drop (M N n : ℕ) (hNM : N≤M) (hn : n≤N) (u : CutoffDepth.Q ℝ M) :
    TensorProjection.piece n (normalVal M u)=
      TensorProjection.piece n (normalVal N (CutoffDiagonal.drop M N hNM u)) := by
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations (∅:Set (A ℝ Bool)) M) u
  change TensorProjection.piece n (normalVal M (quotient ∅ M p))=
    TensorProjection.piece n (normalVal N (CutoffDiagonal.drop M N hNM (quotient ∅ M p)))
  rw [drop_quotient,normalVal_quotient,normalVal_quotient,piece_trunc _ _ (hn.trans hNM),piece_trunc _ _ hn]
 theorem q_embed_any (N n : ℕ) (hn : n≤N) : embed (q n)=TensorProjection.piece n (V N) := by
  have hh := piece_drop N n n hn le_rfl (KZComparison.value N)
  rw [KZCutoffComparison.value_drop] at hh
  rw [hh]
  by_cases h : 0<n
  · exact q_embed n h
  · have he : n=0 := by omega
    subst n
    exact q_embed_zero
 theorem residual_above (N n : ℕ) (hn : n≤N+1) :
    V N-∑ i∈Finset.range n,embed (q i)∈above (fun _ => 1) n := by
  induction n with
  | zero => simpa only [Finset.range_zero,Finset.sum_empty,sub_zero] using TruncatedFree.all_ge_zero (V N)
  | succ n ih =>
    have hh := subtract_piece_above (ih (by omega))
    have he : TensorProjection.piece n (V N-∑ i∈Finset.range n,embed (q i))=embed (q n) := by
      rw [map_sub,map_sum,←q_embed_any N n (by omega)]
      have hz : ∑ i∈Finset.range n,TensorProjection.piece n (embed (q i))=0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [piece_homogeneous (WeightBridge.embed_homogeneous (q_homogeneous i)),if_neg (by have hi' := Finset.mem_range.mp hi; omega)]
      rw [hz,sub_zero]
    rw [he] at hh
    rw [Finset.sum_range_succ]
    simpa only [sub_add_eq_sub_sub] using hh

end RealDeligneDrinfeld.KZHomogeneous

namespace DeligneDrinfeld
end DeligneDrinfeld

namespace RealDeligneDrinfeld.CategoricalValues
open DeligneDrinfeld.CategoryGauge

theorem rotate_squared : rotateLie.comp rotateLie=eval (-x-y) x := by
  apply FreeLieAlgebra.hom_ext
  intro i
  cases i
  · simp [rotateLie,eval,x,y]
  · simp [rotateLie,eval,x,y]
    abel

end RealDeligneDrinfeld.CategoricalValues

namespace RealDeligneDrinfeld.KZHomogeneous

section
open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing
 def assoc (a b : L) : A ℝ Bool →ₐ[ℝ] A ℝ Bool := lift (fun i => if i then embed b else embed a)
 @[simp] theorem assoc_atom (a b : L) (i : Bool) : assoc a b (atom i)=if i then embed b else embed a := lift_atom _ _
 theorem assoc_embed (a b p : L) : assoc a b (embed p)=embed (eval a b p) := by
  have hh : (assoc a b).toLieHom.comp embed=embed.comp (eval a b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    change assoc a b (embed (FreeLieAlgebra.of ℝ i))=embed (eval a b (FreeLieAlgebra.of ℝ i))
    rw [embed_of,assoc_atom]
    cases i <;> simp [eval]
  exact LieHom.congr_fun hh p
 theorem assoc_homogeneous (a b : L) (ha : a∈Ln 1) (hb : b∈Ln 1) (i : Bool) :
    assoc a b (atom i)∈homogeneous (fun _ => 1) 1 := by
  rw [assoc_atom]
  cases i
  · exact WeightBridge.embed_homogeneous ha
  · exact WeightBridge.embed_homogeneous hb
 theorem piece_natural (N n : ℕ) (hn : n≤N) (f : A ℝ Bool →ₐ[ℝ] A ℝ Bool)
    (g : CutoffDepth.Q ℝ N →ₐ[ℝ] CutoffDepth.Q ℝ N)
    (hf : ∀ i,f (atom i)∈homogeneous (fun _ => 1) 1)
    (hg : ∀ i,g (CutoffDepth.gen N i)=quotient ∅ N (f (atom i))) (u : CutoffDepth.Q ℝ N) :
    TensorProjection.piece n (normalVal N (g u))=f (TensorProjection.piece n (normalVal N u)) := by
  have he : g.comp (quotient ∅ N)=(quotient ∅ N).comp f := by
    apply AssociativeElimination.hom_ext
    exact hg
  obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective ℝ (relations (∅:Set (A ℝ Bool)) N) u
  change TensorProjection.piece n (normalVal N (g (quotient ∅ N p)))=
    f (TensorProjection.piece n (normalVal N (quotient ∅ N p)))
  rw [show g (quotient ∅ N p)=quotient ∅ N (f p) from AlgHom.congr_fun he p,
    normalVal_quotient,normalVal_quotient,piece_trunc _ _ hn,piece_trunc _ _ hn]
  exact (algHom_piece f (fun _ => 1) (fun _ => 1) hf n p).symm
 theorem swap_piece (N n : ℕ) (hn : n≤N) (u : CutoffDepth.Q ℝ N) :
    TensorProjection.piece n (normalVal N (KZSwap.swap N u))=
      assoc y x (TensorProjection.piece n (normalVal N u)) := by
  apply piece_natural N n hn _ _ (assoc_homogeneous y x WeightBridge.y_mem WeightBridge.x_mem)
  intro i
  rw [KZSwap.swap_gen,assoc_atom]
  cases i <;> simp only [x,y,embed_of]
  all_goals rfl
 theorem rotate_piece (N n : ℕ) (hn : n≤N) (u : CutoffDepth.Q ℝ N) :
    TensorProjection.piece n (normalVal N (ComplexComparison.realRotate N u))=
      assoc y (-x-y) (TensorProjection.piece n (normalVal N u)) := by
  apply piece_natural N n hn _ _ (assoc_homogeneous y (-x-y) WeightBridge.y_mem
    ((Ln 1).sub_mem ((Ln 1).neg_mem WeightBridge.x_mem) WeightBridge.y_mem))
  intro i
  rw [ComplexComparison.realRotate_gen,assoc_atom]
  cases i
  · simp only [y,embed_of]; rfl
  · change -CutoffDepth.gen N false-CutoffDepth.gen N true=quotient ∅ N (embed (-x-y))
    simp only [map_sub,map_neg,x,y,embed_of]; rfl
 theorem anti (n : ℕ) : q n+eval y x (q n)=0 := by
  apply UniversalEmbedding.injective
  rw [map_add,map_zero,←assoc_embed, q_embed_any n n le_rfl]
  have hh := congrArg (fun u => TensorProjection.piece n (normalVal n u)) (KZSwap.value_swap n)
  rw [swap_piece n n le_rfl,map_neg,map_neg] at hh
  change TensorProjection.piece n (V n)+assoc y x (TensorProjection.piece n (V n))=0
  rw [hh,add_neg_cancel]
 theorem cyclic (n : ℕ) : q n+eval y (-x-y) (q n)+eval (-x-y) x (q n)=0 := by
  have hrot (p : L) : eval y (-x-y) (eval y (-x-y) p)=eval (-x-y) x p :=
    LieHom.congr_fun CategoricalValues.rotate_squared p
  apply UniversalEmbedding.injective
  rw [map_add,map_add,map_zero,←hrot,←assoc_embed,←assoc_embed,←assoc_embed,q_embed_any n n le_rfl]
  have hh := congrArg (fun u => TensorProjection.piece n (normalVal n u)) (ComplexComparison.real_value_cyclic n)
  simpa only [map_add,map_zero,rotate_piece n n le_rfl] using hh
end

open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
open DeligneDrinfeld.LieGrading DeligneDrinfeld.UniversalEmbedding
 theorem value_depth (N : ℕ) : KZComparison.value N∈CutoffDepth.depthSpace N 1 := by
  have hh := (CutoffDepth.depthSpace N 1).add_mem
    (CutoffDepth.depth_antitone N (by omega : 1≤2) (KZComparison.arrow_log_congruence N))
    (KZComparison.arrow_depth N)
  simpa only [sub_add_cancel] using hh
 theorem normal_depth (N : ℕ) : V N∈above GenericIhara.depth 1 := by
  obtain ⟨p,hp,h⟩ := value_depth N
  change CutoffDepth.quotient N p=KZComparison.value N at h
  rw [V,←h,normalVal_quotient]
  exact project_preserves hp
 theorem q_depth (n : ℕ) : embed (q n)∈above GenericIhara.depth 1 := by
  rw [q_embed_any n n le_rfl]
  exact project_preserves (normal_depth n)
 theorem weight_one_form {p : L} (hp : p∈Ln 1) : ∃ a b : ℝ,p=a • x+b • y := by
  rw [Ln,WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    obtain ⟨a,rfl⟩ := LowWeight.tree_degree_one u hu
    cases a
    · exact ⟨1,0,by simp [Tree.eval,x]⟩
    · exact ⟨0,1,by simp [Tree.eval,y]⟩
  | zero => exact ⟨0,0,by simp⟩
  | add p q _ _ hp hq =>
    obtain ⟨a,b,rfl⟩ := hp
    obtain ⟨c,d,rfl⟩ := hq
    exact ⟨a+c,b+d,by simp only [add_smul]; abel⟩
  | smul c p _ hp =>
    obtain ⟨a,b,rfl⟩ := hp
    exact ⟨c*a,c*b,by simp only [smul_add,mul_smul]⟩
 theorem q_one : q 1=0 := by
  classical
  obtain ⟨a,b,h⟩ := weight_one_form (q_homogeneous 1)
  have hd := q_depth 1
  have ha := coeff_support hd (FreeMonoid.of false) (by simp [GenericIhara.depth])
  rw [h,map_add,map_smul,map_smul] at ha
  simp only [MonoidAlgebra.coeff_add,MonoidAlgebra.coeff_smul,x,y,embed_of,atom,MonoidAlgebra.coeff_single] at ha
  norm_num at ha
  change a+Finsupp.single (FreeMonoid.of true) b (FreeMonoid.of false)=0 at ha
  rw [Finsupp.single_eq_of_ne (by intro he; have hh := congrArg FreeMonoid.toList he; simp at hh),add_zero] at ha
  have hs := anti 1
  rw [h,ha,zero_smul,zero_add] at hs
  have hh := congrArg (fun p => MonoidAlgebra.coeff (embed p) (FreeMonoid.of false)) hs
  simp only [map_add,map_smul,map_zero,eval,y,x,FreeLieAlgebra.lift_of_apply,↓reduceIte,embed_of,atom,MonoidAlgebra.coeff_add,MonoidAlgebra.coeff_smul,MonoidAlgebra.coeff_single,MonoidAlgebra.coeff_zero] at hh
  norm_num at hh
  change Finsupp.single (FreeMonoid.of true) b (FreeMonoid.of false)+b=0 at hh
  rw [Finsupp.single_eq_of_ne (by intro he; have hh := congrArg FreeMonoid.toList he; simp at hh),zero_add] at hh
  simp only [h,ha,hh,zero_smul,zero_add]
 def cyc : L →ₗ[ℝ] L := LinearMap.id+(eval y (-x-y)).toLinearMap+(eval (-x-y) x).toLinearMap
 theorem cyclic_weight_two {p : L} (hp : p∈Ln 2) : cyc p=(3 : ℝ) • p := by
  rw [Ln,WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨u,hu,rfl⟩ := hp
    cases u with
    | leaf a => simp at hu
    | node u v =>
      have h1 := LowWeight.treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) u
      have h2 := LowWeight.treeDegree_pos (fun _ : Bool => Nat.zero_lt_one) v
      simp only [treeDegree_node] at hu
      obtain ⟨a,rfl⟩ := LowWeight.tree_degree_one u (by omega)
      obtain ⟨b,rfl⟩ := LowWeight.tree_degree_one v (by omega)
      cases a <;> cases b <;>
        simp [Tree.eval,cyc,eval,x,y,lie_sub,sub_lie,lie_skew,show (3 : ℝ)=(1+1+1) by norm_num,add_smul]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,smul_add]
  | smul c p _ hp => simp only [map_smul,hp,smul_smul,mul_comm]
 theorem q_two : q 2=0 := by
  have hc : cyc (q 2)=0 := cyclic 2
  rw [cyclic_weight_two (q_homogeneous 2)] at hc
  exact (smul_eq_zero.mp hc).resolve_left (by norm_num)
 theorem q_low {n : ℕ} (hn : n≤2) : q n=0 := by
  interval_cases n
  · simp [q]
  · exact q_one
  · exact q_two
end RealDeligneDrinfeld.KZHomogeneous

namespace DeligneDrinfeld.TangentialCutoff

section
open AssociativeElimination WordGrading TruncatedWords
variable {R α : Type*} [CommRing R]
variable (P : Set (A R α)) (N : ℕ)
 variable (d : Module.End R (TruncatedWords.Q P N)) (hd : ∀ a b,d (a*b)=d a*b+a*d b) (h1 : d 1=0)
 include hd h1
 theorem word_mem (k : ℕ) (hv : ∀ a,d (TruncatedDerivation.gen P N a)∈(filtration P N) (k+1)) (w : FreeMonoid α) :
    d (quotient P N (word w))∈(filtration P N) (degree wt w+k) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one,h1]; exact Submodule.zero_mem _
  | of_mul a w ih =>
    rw [word_mul,map_mul,hd,degree_mul,degree_of]
    change _∈(filtration P N) (1+degree wt w+k)
    apply Submodule.add_mem
    · have hw : quotient P N (word w)∈(filtration P N) (degree wt w) := ⟨word w,WordGrading.word_mem w le_rfl,rfl⟩
      simpa only [TruncatedDerivation.gen,word_of,show k+1+degree wt w=1+degree wt w+k by omega] using filtration_mul P N (k+1) _ (hv a) hw
    · simpa only [Nat.add_assoc,wt,TruncatedDerivation.gen,word_of] using
        filtration_mul P N 1 _ (TruncatedDerivation.gen_mem P N a) ih
 theorem mem (k : ℕ) (hv : ∀ a,d (TruncatedDerivation.gen P N a)∈(filtration P N) (k+1))
    (m : ℕ) (a : (TruncatedWords.Q P N)) (ha : a∈(filtration P N) m) : d a∈(filtration P N) (m+k) := by
  obtain ⟨p,hp,rfl⟩ := ha
  exact map_space (d.comp (quotient P N).toLinearMap) _
    (fun w hw => filtration_antitone P N (Nat.add_le_add_right hw k) (word_mem P N d hd h1 k hv w)) hp

end

open AssociativeElimination TruncatedWords
variable {R : Type*} [CommRing R] (N : ℕ)
 theorem difference_mem (d e : Module.End R (TruncatedWords.Q (∅ : Set (A R Bool)) N)) (q r : (TruncatedWords.Q (∅ : Set (A R Bool)) N))
    (hd : ∀ a b,d (a*b)=d a*b+a*d b) (he : ∀ a b,e (a*b)=e a*b+a*e b)
    (hd1 : d 1=0) (he1 : e 1=0) (hdx : d (TruncatedDerivation.gen (∅ : Set (A R Bool)) N false)=0) (hex : e (TruncatedDerivation.gen (∅ : Set (A R Bool)) N false)=0)
    (hdy : d (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)=(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)*q-q*(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)) (hey : e (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)=(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)*r-r*(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true))
    (k : ℕ) (hq : q-r∈(filtration (∅ : Set (A R Bool)) N) k) (m : ℕ) (a : (TruncatedWords.Q (∅ : Set (A R Bool)) N)) (ha : a∈(filtration (∅ : Set (A R Bool)) N) m) :
    d a+q*a-(e a+r*a)∈(filtration (∅ : Set (A R Bool)) N) (m+k) := by
  have hm : (d-e) a∈(filtration (∅ : Set (A R Bool)) N) (m+k) := by
    apply mem ∅ N (d-e) (fun a b => ?_) (by simp only [LinearMap.sub_apply,hd1,he1,sub_self])
      k (fun b => ?_) m a ha
    · simp only [LinearMap.sub_apply,hd,he,sub_mul,mul_sub]
      abel
    · cases b
      · simp only [LinearMap.sub_apply,hdx,hex,sub_self,Submodule.zero_mem]
      · change d (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)-e (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)∈_
        rw [hdy,hey]
        have hy := TruncatedDerivation.gen_mem (∅:Set (A R Bool)) N true
        have hm1 := filtration_mul ∅ N 1 k hy hq
        have hm2 := filtration_mul ∅ N k 1 hq hy
        have hh : (TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)*(q-r)-(q-r)*(TruncatedDerivation.gen (∅ : Set (A R Bool)) N true)∈(filtration (∅ : Set (A R Bool)) N) (k+1) :=
          ((filtration (∅ : Set (A R Bool)) N) (k+1)).sub_mem (by simpa only [Nat.add_comm 1 k] using hm1) hm2
        convert hh using 1; simp only [mul_sub,sub_mul]; abel
  have hq' : (q-r)*a∈(filtration (∅ : Set (A R Bool)) N) (m+k) := by
    simpa only [Nat.add_comm k m] using filtration_mul ∅ N k m hq ha
  convert ((filtration (∅ : Set (A R Bool)) N) (m+k)).add_mem hm hq' using 1
  simp only [LinearMap.sub_apply,sub_mul]
  abel
end DeligneDrinfeld.TangentialCutoff

namespace DeligneDrinfeld.PresentedSubstitution
open AssociativeElimination WordGrading TruncatedWords
variable {R α β : Type*} [CommRing R] (P : Set (A R β)) (N : ℕ)
variable (f : α → TruncatedWords.Q P N) (hf : ∀ a,f a∈filtration P N 1)
include hf
 theorem subst_mem {n : ℕ} {a : TruncatedWords.Q (∅:Set (A R α)) N}
    (ha : a∈filtration ∅ N n) : subst P N f hf a∈filtration P N n := by
  obtain ⟨a,ha,rfl⟩ := ha
  change subst P N f hf (quotient ∅ N a)∈_
  rw [subst_quotient]
  exact lift_mem P N f hf ha
end DeligneDrinfeld.PresentedSubstitution

namespace DeligneDrinfeld.PresentedCutoff
open AssociativeElimination WordGrading TruncatedWords
variable {R α M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
attribute [local instance] LieRing.ofAssociativeRing
variable (P : Set (A R α)) (N : ℕ)
local notation "Q" => TruncatedWords.Q P N

 theorem raw_embed (d : LieDerivation R M M) (e : FreeLieAlgebra R α →ₗ⁅R⁆ M)
    (j : M →ₗ⁅R⁆ Q) (hj : ∀ a,j (e (FreeLieAlgebra.of R a))=TruncatedDerivation.gen P N a)
    (p : FreeLieAlgebra R α) :
    TruncatedDerivation.raw P N (fun a => j (d (e (FreeLieAlgebra.of R a)))) (embed p)=j (d (e p)) := by
  have he : (quotient P N).toLieHom.comp embed=j.comp e := by
    apply FreeLieAlgebra.hom_ext
    intro a
    change quotient P N (embed (FreeLieAlgebra.of R a))=j (e (FreeLieAlgebra.of R a))
    rw [embed_of,hj]; rfl
  have he' (p : FreeLieAlgebra R α) : quotient P N (embed p)=j (e p) := LieHom.congr_fun he p
  induction p using freeLie_induction with
  | h0 => simp
  | hg a => rw [embed_of,TruncatedDerivation.raw_atom]
  | ha a b ha hb => simp only [map_add,ha,hb]
  | hs r a ha => simp only [map_smul,ha]
  | hl a b ha hb =>
    simp only [LieHom.map_lie,LieDerivation.apply_lie_eq_add,map_add]
    change TruncatedDerivation.raw P N _ (embed a*embed b-embed b*embed a)=_
    rw [map_sub,TruncatedDerivation.raw_mul,TruncatedDerivation.raw_mul,ha,hb,he',he']
    simp only [Ring.lie_def]
    noncomm_ring

 theorem derivation_embed (k : ℕ) (v : α → Q) (hv : ∀ a,v a∈filtration P N (k+1))
    (hP : ∀ p∈P,TruncatedDerivation.raw P N v p=0)
    (d : LieDerivation R M M) (e : FreeLieAlgebra R α →ₗ⁅R⁆ M)
    (j : M →ₗ⁅R⁆ Q) (hj : ∀ a,j (e (FreeLieAlgebra.of R a))=TruncatedDerivation.gen P N a)
    (hv' : ∀ a,v a=j (d (e (FreeLieAlgebra.of R a)))) (p : FreeLieAlgebra R α) :
    TruncatedDerivation.derivation P N k v hv hP (quotient P N (embed p))=j (d (e p)) := by
  rw [TruncatedDerivation.derivation_quotient]
  have he : v=(fun a => j (d (e (FreeLieAlgebra.of R a)))) := funext hv'
  rw [he]
  exact raw_embed P N d e j hj p

end DeligneDrinfeld.PresentedCutoff

end

end OAI

end


section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.FreeCutoffCategory
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing

 theorem d_mem {n m : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) {a : Q N} (ha : a∈F N m) :
    d N hq a∈F N (m+n) := DeligneDrinfeld.TruncatedDerivation.derivation_mem P N n _ _ _ ha
 theorem d_j {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : L) :
    d N hq (j N p)=j N (RealDeligneDrinfeld.derivation q p) :=
  DeligneDrinfeld.PresentedCutoff.derivation_embed P N n _ _ _ (RealDeligneDrinfeld.derivation q)
    (LieHom.id) (j N) (j_of N) (fun _ => rfl) p

 theorem h_mem {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : Fin 3) : h N q p∈F N n := by
  have hr : CategoricalValues.rotateLie q∈Ln n :=
    WeightBridge.eval_mem hq WeightBridge.y_mem ((Ln 1).sub_mem ((Ln 1).neg_mem WeightBridge.x_mem) WeightBridge.y_mem)
  unfold h ThreeSolutionCategory.data
  fin_cases p
  · change j N 0∈F N n; rw [map_zero]; exact Submodule.zero_mem _
  · exact j_mem hq
  · exact j_mem ((Ln n).add_mem hq hr)

 theorem loop_j {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p : Fin 3) (a : L) :
    (data N hq).D p p (j N a)=j N (DeligneDrinfeld.CategoryGauge.loop (ThreeSolutionCategory.data q) p a) := by
  change d N hq (j N a)+h N q p*j N a-j N a*h N q p=_
  rw [d_j,DeligneDrinfeld.CategoryGauge.loop_apply,map_add,LieHom.map_lie,Ring.lie_def]
  change _=j N (RealDeligneDrinfeld.derivation q a)+(h N q p*j N a-j N a*h N q p)
  abel

 theorem raises {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) (p s : Fin 3)
    (m : ℕ) (a : Q N) (ha : a∈F N m) : (data N hq).D p s a∈F N (m+n) :=
  DeligneDrinfeld.CutoffCategory.raises P N (d N hq) (d_mul N hq) (d_one N hq) (h N q) n
    (fun _ _ ha => d_mem N hq ha) (h_mem N hq) p s m a ha

 theorem unit {n : ℕ} (N : ℕ) {q : L} (hq : q∈Ln n) : (data N hq).D 0 1 1=j N q := by
  change (d N hq 1+h N q 1*1)-1*h N q 0=_
  rw [d_one]
  simp [h,ThreeSolutionCategory.data]

end RealDeligneDrinfeld.FreeCutoffCategory

namespace RealDeligneDrinfeld.BraidCutoff
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords
attribute [local instance] LieRing.ofAssociativeRing

 theorem projection_relation {p : BraidFree} (hp : p∈braidRelations) : projection p=0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr (LieSubmodule.subset_lieSpan hp)

open T4Basic T4SolutionData
variable {n : ℕ} {q : L}

end RealDeligneDrinfeld.BraidCutoff

namespace RealDeligneDrinfeld.BraidInsertionExp
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.CategoryGauge
attribute [local instance] LieRing.ofAssociativeRing
variable (N : ℕ) (X Y : T4)
  (hX : BraidCutoff.lieMap N X∈BraidCutoff.F N 1) (hY : BraidCutoff.lieMap N Y∈BraidCutoff.F N 1)
 theorem insert_gen (a : Bool) : insert N X Y hX hY (DeligneDrinfeld.TruncatedDerivation.gen ∅ N a)=family N X Y a :=
  DeligneDrinfeld.PresentedSubstitution.subst_gen _ _ _ _ a
 theorem insert_j (p : L) : insert N X Y hX hY (FreeCutoffCategory.j N p)=BraidCutoff.lieMap N (eval X Y p) := by
  have he : (insert N X Y hX hY).toLieHom.comp (FreeCutoffCategory.j N)=
      (BraidCutoff.lieMap N).comp (eval X Y) := by
    apply FreeLieAlgebra.hom_ext
    intro a
    change insert N X Y hX hY (FreeCutoffCategory.j N (FreeLieAlgebra.of ℝ a))=_
    rw [FreeCutoffCategory.j_of,insert_gen]
    cases a <;> simp [family,eval]
  exact LieHom.congr_fun he p

 variable {n : ℕ} {q : L} (hq : q∈W) (hqn : q∈Ln n) (hn : 2<n)

 open T4Basic

end RealDeligneDrinfeld.BraidInsertionExp

namespace DeligneDrinfeld.CategoryExp
variable {R A B O P I : Type*} [CommRing R] [Ring A] [Algebra R A]
  [Ring B] [Algebra R B]
 theorem sum_apply (s : Finset I) (g : I → Data R A O) (p q : O) (a : A) :
    (sum s g).D p q a=∑ i∈s,(g i).D p q a := LinearMap.sum_apply _ _ _
 theorem sum_raises {N : ℕ} (F : FilteredComparison.Filtration R A N)
    (s : Finset I) (g : I → Data R A O)
    (hg : ∀ i∈s,∀ p q m a,a∈F.step m → (g i).D p q a∈F.step (m+1))
    (p q : O) (m : ℕ) (a : A) (ha : a∈F.step m) :
    (sum s g).D p q a∈F.step (m+1) := by
  rw [sum_apply]
  exact Submodule.sum_mem _ (fun i hi => hg i hi p q m a ha)
end DeligneDrinfeld.CategoryExp

section

namespace RealDeligneDrinfeld.BraidInsertionSum
open DeligneDrinfeld.CategoryExp
open BraidInsertionExp
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hq : ∀ i,q i∈W) (hqn : ∀ i,q i∈Ln (n i)) (hn : ∀ i,2<n i)
 include hn in
 theorem free_raises (p r : Fin 3) (m : ℕ) (a : FreeCutoffCategory.Q N) (ha : a∈FreeCutoffCategory.F N m) :
    (free N s q n hqn).D p r a∈FreeCutoffCategory.F N (m+1) := by
  apply sum_raises (DeligneDrinfeld.CutoffCategory.filtration ∅ N) s _ _ p r m a ha
  intro i _hi p r m a ha
  exact DeligneDrinfeld.TruncatedWords.filtration_antitone ∅ N (by have := hn i; omega)
    (FreeCutoffCategory.raises N (hqn i) p r m a ha)
 theorem unit : (free N s q n hqn).D 0 1 1=FreeCutoffCategory.j N (∑ i∈s,q i) := by
  rw [free,DeligneDrinfeld.CategoryExp.sum_apply,map_sum]
  exact Finset.sum_congr rfl (fun i _hi => FreeCutoffCategory.unit N (hqn i))
 theorem edge_formula (a : FreeCutoffCategory.Q N) :
    (free N s q n hqn).D 0 1 a=(free N s q n hqn).D 0 0 a+FreeCutoffCategory.j N (∑ i∈s,q i)*a := by
  have hh := (free N s q n hqn).comp 0 0 1 a 1
  rw [one_mul,one_mul,unit] at hh
  rw [hh,add_comm]
end RealDeligneDrinfeld.BraidInsertionSum

end

namespace DeligneDrinfeld.CategoryExp
open IsNilpotent
variable {R V : Type*} [CommRing R] [Algebra ℚ R] [AddCommGroup V]
  [Module R V] [Module ℚ V] [IsScalarTower ℚ R V]
variable {N : ℕ} (F : FilteredComparison.Filtration R V N)
  (A B : Module.End R V) (k : ℕ)
  (hA : ∀ m a,a∈F.step m → A a∈F.step (m+1))
  (hB : ∀ m a,a∈F.step m → B a∈F.step (m+1))
  (hD : ∀ m a,a∈F.step m → A a-B a∈F.step (m+k))
include hA hB hD
 omit [Algebra ℚ R] [Module ℚ V] [IsScalarTower ℚ R V] in
 theorem pow_difference (i m : ℕ) {a : V} (ha : a∈F.step m) :
    (A^(i+1)) a-(B^(i+1)) a∈F.step (m+k+i) := by
  induction i with
  | zero => simpa only [zero_add,pow_one,Nat.add_zero] using hD m a ha
  | succ i ih =>
    have h₁ := hA (m+k+i) _ ih
    rw [map_sub] at h₁
    have hp := pow_mem_shift F B 1 hB (i+1) m ha
    simp only [Nat.mul_one] at hp
    have h₂ := hD (m+(i+1)) _ hp
    have hh := (F.step (m+k+i+1)).add_mem h₁ (by convert h₂ using 1; congr 1; omega)
    rw [pow_succ' A (i+1),pow_succ' B (i+1),Module.End.mul_apply,Module.End.mul_apply]
    convert hh using 1 <;> first | abel | omega

 theorem exp_difference (m : ℕ) {a : V} (ha : a∈F.step m) :
    exp A a-exp B a-(A a-B a)∈F.step (m+k+1) := by
  have hnil (d : Module.End R V) (hd : ∀ m a,a∈F.step m → d a∈F.step (m+1)) : d^(N+1)=0 := by
    apply LinearMap.ext
    intro x
    have hh := pow_mem_shift F d 1 hd (N+1) 0 (a:=x) (by rw [F.initial]; trivial)
    simpa only [Nat.mul_one,Nat.zero_add,F.terminal,Submodule.mem_bot,LinearMap.zero_apply] using hh
  let r := N+1
  let s := N+1
  have hr : A^r=0 := hnil A hA
  have hs : B^s=0 := hnil B hB
  have hr' : A^(2+(r+s))=0 := pow_eq_zero_of_le (by omega) hr
  have hs' : B^(2+(r+s))=0 := pow_eq_zero_of_le (by omega) hs
  rw [exp_eq_sum hr',exp_eq_sum hs',LinearMap.sum_apply,LinearMap.sum_apply,
    ←Finset.sum_sub_distrib,Finset.sum_range_add]
  have ht : (∑ i∈Finset.range 2,(((↑i.factorial:ℚ)⁻¹ • A^i) a-((↑i.factorial:ℚ)⁻¹ • B^i) a))=A a-B a := by
    simp [Finset.sum_range_succ]
  rw [ht,add_sub_cancel_left]
  apply Submodule.sum_mem
  intro i hi
  simp only [LinearMap.smul_apply,←smul_sub]
  apply ((F.step (m+k+1)).restrictScalars ℚ).smul_mem
  have hh := pow_difference F A B k hA hB hD (i+1) m ha
  have he : 2+i=i+1+1 := by omega
  rw [he]
  exact F.decreasing (by omega) hh

 theorem exp_difference_unit {a u : V} (ha : a-u∈F.step 1) :
    exp A a-exp B a-(A u-B u)∈F.step (k+1) := by
  have h₁ := exp_difference F A B k hA hB hD 0 (a:=a) (by rw [F.initial]; trivial)
  have h₂ := hD 1 (a-u) ha
  rw [map_sub,map_sub] at h₂
  have h₁' : exp A a-exp B a-(A a-B a)∈F.step (k+1) := by simpa only [Nat.zero_add] using h₁
  have h₂' : A a-A u-(B a-B u)∈F.step (k+1) := by simpa only [Nat.add_comm 1 k] using h₂
  convert (F.step (k+1)).add_mem h₁' h₂' using 1; abel
end DeligneDrinfeld.CategoryExp

end

end OAI

end

section

namespace OAI

noncomputable section

section
namespace RealDeligneDrinfeld.BraidInsertionSum
open DeligneDrinfeld.CategoryExp
attribute [local instance] LieRing.ofAssociativeRing
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hqn : ∀ i,q i∈Ln (n i))
 theorem loop_x : (free N s q n hqn).D 0 0 (FreeCutoffCategory.j N x)=0 := by
  rw [free,DeligneDrinfeld.CategoryExp.sum_apply]
  apply Finset.sum_eq_zero
  intro i _hi
  rw [FreeCutoffCategory.loop_j]
  rw [DeligneDrinfeld.CategoryGauge.loop_apply]
  change FreeCutoffCategory.j N (derivation (q i) x+⁅(0:L),x⁆)=0
  rw [derivation_apply,D_x,zero_lie,add_zero,map_zero]
 theorem loop_y : (free N s q n hqn).D 0 0 (FreeCutoffCategory.j N y)=
    FreeCutoffCategory.j N y*FreeCutoffCategory.j N (∑ i∈s,q i)-
      FreeCutoffCategory.j N (∑ i∈s,q i)*FreeCutoffCategory.j N y := by
  rw [free,DeligneDrinfeld.CategoryExp.sum_apply,map_sum,Finset.mul_sum,Finset.sum_mul,←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [FreeCutoffCategory.loop_j]
  rw [DeligneDrinfeld.CategoryGauge.loop_apply]
  change FreeCutoffCategory.j N (derivation (q i) y+⁅(0:L),y⁆)=_
  rw [derivation_apply,D_y,zero_lie,add_zero,LieHom.map_lie,Ring.lie_def]
end RealDeligneDrinfeld.BraidInsertionSum

namespace RealDeligneDrinfeld.KZLogDifference
open DeligneDrinfeld DeligneDrinfeld.KZRealLog DeligneDrinfeld.KZComparison
open BraidInsertionSum
variable {I : Type*} (N : ℕ) (s : Finset I) (q : I → L) (n : I → ℕ)
  (hqn : ∀ i,q i∈Ln (n i)) (hn : ∀ i,2<n i)
 theorem difference (k : ℕ)
    (hq : KZComparison.value N-FreeCutoffCategory.j N (∑ i∈s,q i)∈FreeCutoffCategory.F N k)
    (m : ℕ) (a : FreeCutoffCategory.Q N) (ha : a∈FreeCutoffCategory.F N m) :
    KZRealLog.D N false true a-(free N s q n hqn).D 0 1 a∈FreeCutoffCategory.F N (m+k) := by
  rw [KZRealLog.edge_formula,BraidInsertionSum.edge_formula]
  apply TangentialCutoff.difference_mem N (KZRealLog.D N false false) ((free N s q n hqn).D 0 0)
      (KZComparison.value N) (FreeCutoffCategory.j N (∑ i∈s,q i))
      (fun a b => (KZRealLog.data N).comp false false false b a) (fun a b => (free N s q n hqn).comp 0 0 0 b a)
      ((KZRealLog.data N).one false) ((free N s q n hqn).one 0)
  · exact KZRealLog.loop_x N
  · simpa only [x,FreeCutoffCategory.j_of] using BraidInsertionSum.loop_x N s q n hqn
  · exact KZRealLog.loop_false_y N
  · simpa only [y,FreeCutoffCategory.j_of] using BraidInsertionSum.loop_y N s q n hqn
  · exact hq
  · exact ha
 include hn in
 theorem exponential (k : ℕ)
    (hq : KZComparison.value N-FreeCutoffCategory.j N (∑ i∈s,q i)∈FreeCutoffCategory.F N k) :
    (negative N:FreeCutoffCategory.Q N)-CategoryExp.act (free N s q n hqn) 0 1 (positive N)-
      (KZComparison.value N-FreeCutoffCategory.j N (∑ i∈s,q i))∈FreeCutoffCategory.F N (k+1) := by
  have hh := CategoryExp.exp_difference_unit (CutoffCategory.filtration ∅ N)
    (KZRealLog.D N false true) ((free N s q n hqn).D 0 1) k
    (KZRealLog.raises N false true) (free_raises N s q n hqn hn 0 1)
    (difference N s q n hqn k hq) (positive_weight N)
  rw [KZRealLog.exp_comparison,KZRealLog.value,BraidInsertionSum.unit] at hh
  exact hh
end RealDeligneDrinfeld.KZLogDifference

end

end

end OAI

end


section

namespace OAI

noncomputable section

namespace RealDeligneDrinfeld.KZBraidPentagon
open DeligneDrinfeld DeligneDrinfeld.FinitePicard DeligneDrinfeld.KZCollar
open BraidInsertionExp T4Basic
attribute [local instance] LieRing.ofAssociativeRing
local instance (N : ℕ) : NormedRing (BraidCutoff.Q N) := FiniteAlgebraNorm.normedRing _
local instance (N : ℕ) : NormedAlgebra ℝ (BraidCutoff.Q N) := FiniteAlgebraNorm.normedAlgebra _
def F (N : ℕ) : NilpotentFiltration (BraidCutoff.Q N) where
  space := BraidCutoff.F N
  antitone := TruncatedWords.filtration_antitone _ N
  one_mem := TruncatedWords.filtration_one _ N
  mul_mem := TruncatedWords.filtration_mul _ N
  cutoff := N
  terminal := TruncatedWords.filtration_terminal _ N

def generic (N : ℕ) (s : ℝ) : GenericBraid.T ℝ (Fin 4) →ₗ⁅ℝ⁆ BraidCutoff.Q N :=
  GenericBraid.lift (fun i j => s • BraidCutoff.lieMap N (t i j))
    (by intro i; rw [t_self,map_zero,smul_zero])
    (by intro i j; rw [t_comm i j])
    (by
      intro i j k l hik hil hjk hjl
      by_cases hij : i=j
      · subst j; rw [t_self,map_zero,smul_zero,zero_lie]
      by_cases hkl : k=l
      · subst l; rw [t_self,map_zero,smul_zero,lie_zero]
      rw [smul_lie,lie_smul,←LieHom.map_lie,t_disjoint i j k l hij hik hil hjk hjl hkl,map_zero,smul_zero,smul_zero])
    (by intro i j k hij hik hjk
        rw [←smul_add,←map_add,smul_lie,lie_smul,←LieHom.map_lie,t_three i j k hij hik hjk,map_zero,smul_zero,smul_zero])
@[simp] theorem generic_t (N : ℕ) (s : ℝ) (i j : Fin 4) :
    generic N s (GenericBraid.t i j)=s • BraidCutoff.lieMap N (t i j) := GenericBraid.lift_t _ _ _ _ _ _ _
theorem chords_mem (N : ℕ) (s : ℝ) (i : Fin 6) : KZRectangle.chords (generic N s) i∈(F N).space 1 := by
  fin_cases i <;> simp only [KZRectangle.chords,generic_t] <;>
    exact Submodule.smul_mem _ s (BraidCutoff.t_mem N _ _)
theorem insert_associator (N : ℕ) (s : ℝ) (X Y : T4) (hX hY) :
    insert N X Y hX hY (associator (CutoffKZ.weight N) (s • CutoffKZ.X N) (s • CutoffKZ.Y N))=
      associator (F N) (s • BraidCutoff.lieMap N X) (s • BraidCutoff.lieMap N Y) := by
  rw [map_associator (insert N X Y hX hY) (CutoffKZ.weight N) (F N) rfl
    (Submodule.smul_mem _ s (CutoffDepth.gen_weight N false))
    (Submodule.smul_mem _ s (CutoffDepth.gen_weight N true)),map_smul,map_smul]
  rw [show insert N X Y hX hY (CutoffKZ.X N)=BraidCutoff.lieMap N X from insert_gen N X Y hX hY false,
    show insert N X Y hX hY (CutoffKZ.Y N)=BraidCutoff.lieMap N Y from insert_gen N X Y hX hY true]
theorem pentagon (N : ℕ) (s : ℝ) :
    let u := associator (CutoffKZ.weight N) (s • CutoffKZ.X N) (s • CutoffKZ.Y N)
    IDE N u*IAD N u=ICE N u*IBC N u*IAB N u := by
  dsimp only
  let u := associator (CutoffKZ.weight N) (s • CutoffKZ.X N) (s • CutoffKZ.Y N)
  have hDE : IDE N u=associator (F N) (s • BraidCutoff.lieMap N a) (s • BraidCutoff.lieMap N (b+e)) := insert_associator N s _ _ _ _
  have hAD : IAD N u=associator (F N) (s • BraidCutoff.lieMap N (d+b)) (s • BraidCutoff.lieMap N c) := insert_associator N s _ _ _ _
  have hCE : ICE N u=associator (F N) (s • BraidCutoff.lieMap N b) (s • BraidCutoff.lieMap N c) := insert_associator N s _ _ _ _
  have hBC : IBC N u=associator (F N) (s • BraidCutoff.lieMap N (a+d)) (s • BraidCutoff.lieMap N (e+c)) := insert_associator N s _ _ _ _
  have hAB : IAB N u=associator (F N) (s • BraidCutoff.lieMap N a) (s • BraidCutoff.lieMap N b) := insert_associator N s _ _ _ _
  change IDE N u*IAD N u=ICE N u*IBC N u*IAB N u
  rw [hDE,hAD,hCE,hBC,hAB]
  have hh := FourFrames.associator_pentagon (F N) (generic N s) (chords_mem N s)
  simpa [KZRectangle.chords,KZRectangle.edges,smul_add,a,b,c,d,e] using hh
 theorem positive (N : ℕ) : IDE N (KZComparison.positive N)*IAD N (KZComparison.positive N)=
    ICE N (KZComparison.positive N)*IBC N (KZComparison.positive N)*IAB N (KZComparison.positive N) := by
  simpa only [one_smul,KZComparison.positive_val] using pentagon N 1
 theorem negative (N : ℕ) : IDE N (KZComparison.negative N)*IAD N (KZComparison.negative N)=
    ICE N (KZComparison.negative N)*IBC N (KZComparison.negative N)*IAB N (KZComparison.negative N) := by
  simpa only [neg_one_smul,KZComparison.negative_val] using pentagon N (-1)
end RealDeligneDrinfeld.KZBraidPentagon

namespace DeligneDrinfeld.LieCutoffFaithful
open AssociativeElimination WordGrading TruncatedWords TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
variable {R α M : Type*} [CommRing R] [LieRing M] [LieAlgebra R M]
abbrev S (R : Type*) [CommRing R] (N : ℕ) := TruncatedWords.Q (∅ : Set (A R Unit)) N

def z (N : ℕ) : S R N := quotient ∅ N (atom ())

 theorem z_pow (N n : ℕ) : (z (R:=R) N)^n=quotient ∅ N (word ((FreeMonoid.of ())^n)) := by
  induction n with
  | zero => simp only [pow_zero,word_one,map_one]
  | succ n ih => rw [pow_succ,pow_succ,word_mul,map_mul,←ih,word_of]; rfl
 theorem z_pow_zero {N n : ℕ} (hn : N<n) : (z (R:=R) N)^n=0 := by
  rw [z_pow]
  apply quotient_above ∅ N
  apply word_mem
  have hd : degree (wt : Unit → ℕ) ((FreeMonoid.of ())^n)=n := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,degree_mul,ih,degree_of]
  rw [hd]
  omega

variable {B : Type*} [Ring B] [Algebra R B]
def lift (N : ℕ) (g : α → B) : A R α →ₐ[R] (S R N ⊗[R] B) :=
  AssociativeElimination.lift (R:=R) (B:=S R N ⊗[R] B) (fun a => z N ⊗ₜ[R] g a)

 @[simp] theorem lift_atom (N : ℕ) (g : α → B) (a : α) : lift (R:=R) N g (atom a)=z N ⊗ₜ[R] g a := by
  unfold lift
  exact AssociativeElimination.lift_atom (R:=R) (B:=S R N ⊗[R] B) _ a

 theorem lift_word (N : ℕ) (g : α → B) (w : FreeMonoid α) :
    lift N g (word w)=(z (R:=R) N ^ (degree wt w)) ⊗ₜ[R] AssociativeElimination.lift (R:=R) g (word w) := by
  induction w using FreeMonoid.inductionOn' with
  | one => simp only [word_one,map_one,degree_one,pow_zero,Algebra.TensorProduct.one_def]
  | of_mul a w ih =>
    simp only [word_mul,word_of,map_mul,lift_atom,AssociativeElimination.lift_atom,ih,degree_mul,degree_of]
    rw [Algebra.TensorProduct.tmul_mul_tmul,←pow_succ']
    simp only [wt,Nat.add_comm 1]

 theorem lift_above (N : ℕ) (g : α → B) {p : A R α} (hp : p∈above wt (N+1)) : lift N g p=0 := by
  have hh : lift N g p∈(⊥ : Submodule R (_)) := map_space (lift N g).toLinearMap _ (fun w hw => by
    change lift N g (word w)=0
    rw [lift_word,z_pow_zero (by omega),zero_tmul]) hp
  exact hh

variable [Algebra ℝ B]

 theorem lift_weight {wtL : α → ℕ} (hwt : ∀ a,wtL a=1) (N : ℕ) (g : α → B)
    {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : RealDeligneDrinfeld.WeightedWord wtL n p) :
    lift (R:=ℝ) N g (embed p)=(z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] FreeLieAlgebra.lift ℝ g p := by
  induction hp with
  | generator a =>
    rw [embed_of]
    simp only [LieCutoffFaithful.lift,AssociativeElimination.lift_atom,FreeLieAlgebra.lift_of_apply,hwt,pow_one]
  | @bracket n m a b ha hb ia ib =>
    rw [LieHom.map_lie]
    change lift (R:=ℝ) N g (embed _*embed _-embed _*embed _)=_
    rw [map_sub,map_mul,map_mul,ia,ib,Algebra.TensorProduct.tmul_mul_tmul,
      Algebra.TensorProduct.tmul_mul_tmul,←pow_add,←pow_add,Nat.add_comm m n]
    rw [←tmul_sub,LieHom.map_lie,Ring.lie_def]

 theorem lift_piece (N : ℕ) (g : α → B) {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈RealDeligneDrinfeld.weightPiece (fun _ : α => 1) n) :
    lift (R:=ℝ) N g (embed p)=(z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] FreeLieAlgebra.lift ℝ g p := by
  apply Submodule.span_induction (p:=fun p _ => lift (R:=ℝ) N g (embed p)=
    (z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] FreeLieAlgebra.lift ℝ g p) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact lift_weight (fun _ => rfl) N g hp
  · simp only [map_zero,tmul_zero]
  · intro p q _ _ hp hq; simp only [map_add,hp,hq,tmul_add]
  · intro s p _ hp; simp only [map_smul,hp,tmul_smul]

 theorem coefficient_z_pow {N n : ℕ} (hn : n≤N) :
    TruncatedFree.coefficient N ((FreeMonoid.of ())^n) (z (R:=ℝ) N ^ n)=1 := by
  rw [z_pow,TruncatedFree.coefficient_quotient]
  have hd : degree (wt : Unit → ℕ) ((FreeMonoid.of ())^n)=n := by
    clear hn
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ,degree_mul,ih,degree_of]
  simp only [hd,if_pos hn,word,MonoidAlgebra.coeff_single,Finsupp.single_eq_same]

 def extract (N n : ℕ) : S ℝ N ⊗[ℝ] B →ₗ[ℝ] B :=
  (TensorProduct.lid ℝ B).toLinearMap.comp
    (TensorProduct.map (TruncatedFree.coefficient N ((FreeMonoid.of ())^n)) (LinearMap.id))

 theorem extract_tmul {N n : ℕ} (hn : n≤N) (b : B) :
    extract N n ((z (R:=ℝ) N ^ n) ⊗ₜ[ℝ] b)=b := by
  change TruncatedFree.coefficient N ((FreeMonoid.of ())^n) (z (R:=ℝ) N ^ n) • b=b
  rw [coefficient_z_pow hn,one_smul]

end DeligneDrinfeld.LieCutoffFaithful

namespace RealDeligneDrinfeld.AffineWeight
variable {M : Type*} [LieRing M] [LieAlgebra ℝ M]
attribute [local instance] LieRing.ofAssociativeRing

def op (a b : M) : Module.End ℝ (M × ℝ) where
  toFun v := (⁅a,v.1⁆+v.2 • b,0)
  map_add' v w := by ext <;> simp only [Prod.fst_add,Prod.snd_add,lie_add,add_smul] <;> abel
  map_smul' c v := by
    apply Prod.ext
    · change ⁅a,c • v.1⁆+(c*v.2) • b=c • (⁅a,v.1⁆+v.2 • b)
      rw [lie_smul,smul_add,smul_smul]
    · change (0:ℝ)=c*0
      exact (mul_zero c).symm

 theorem op_lie (a b c d : M) : ⁅op a b,op c d⁆=op ⁅a,c⁆ (⁅b,c⁆+⁅a,d⁆) := by
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · change (⁅a,⁅c,v.1⁆+v.2 • d⁆+0 • b)-(⁅c,⁅a,v.1⁆+v.2 • b⁆+0 • d)=
      ⁅⁅a,c⁆,v.1⁆+v.2 • (⁅b,c⁆+⁅a,d⁆)
    simp only [zero_smul,add_zero,smul_add,lie_add,lie_smul]
    rw [lie_lie,←lie_skew b c,smul_neg]
    abel
  · change (0:ℝ)-0=0
    exact sub_self _

 def homogeneous (n : ℕ) : M →ₗ[ℝ] Module.End ℝ (M×ℝ) where
  toFun a := op a ((n:ℝ) • a)
  map_add' a b := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅a+b,v.1⁆+v.2 • ((n:ℝ) • (a+b))=
        (⁅a,v.1⁆+v.2 • ((n:ℝ) • a))+(⁅b,v.1⁆+v.2 • ((n:ℝ) • b))
      simp only [add_lie,smul_add]; abel
    · change (0:ℝ)=0+0; simp
  map_smul' s a := by
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · change ⁅s • a,v.1⁆+v.2 • ((n:ℝ) • (s • a))=s • (⁅a,v.1⁆+v.2 • ((n:ℝ) • a))
      rw [smul_lie,smul_add,smul_comm (n:ℝ) s,smul_comm v.2 s]
    · change (0:ℝ)=s*0; simp

 theorem homogeneous_lie (n m : ℕ) (a b : M) :
    homogeneous (n+m) ⁅a,b⁆=⁅homogeneous n a,homogeneous m b⁆ := by
  change op ⁅a,b⁆ (((n+m:ℕ):ℝ) • ⁅a,b⁆)=⁅op a ((n:ℝ) • a),op b ((m:ℝ) • b)⁆
  rw [op_lie,smul_lie,lie_smul,Nat.cast_add,add_smul]

 variable {α : Type*}
 def representation (f : α → M) : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ Module.End ℝ (M×ℝ) :=
  FreeLieAlgebra.lift ℝ (fun a => homogeneous 1 (f a))

 theorem word_rep (f : α → M) {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : WeightedWord (fun _ : α => 1) n p) :
    representation f p=homogeneous n (FreeLieAlgebra.lift ℝ f p) := by
  induction hp with
  | generator a => simp only [representation,FreeLieAlgebra.lift_of_apply]
  | bracket ha hb ia ib => rw [LieHom.map_lie,ia,ib,LieHom.map_lie,homogeneous_lie]

 theorem weight_rep (f : α → M) {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈weightPiece (fun _ : α => 1) n) :
    representation f p=homogeneous n (FreeLieAlgebra.lift ℝ f p) := by
  apply Submodule.span_induction (p:=fun p _ => representation f p=homogeneous n (FreeLieAlgebra.lift ℝ f p)) ?_ ?_ ?_ ?_ hp
  · intro p hp; exact word_rep f hp
  · simp only [map_zero]
  · intro p q _ _ hp hq; simp only [map_add,hp,hq]
  · intro s p _ hp; simp only [map_smul,hp]

 theorem homogeneous_injective {n : ℕ} (hn : 0<n) : Function.Injective (homogeneous (M:=M) n) := by
  intro p q h
  have hh := congrArg (fun (F : Module.End ℝ (M×ℝ)) => (F (0,1)).1) h
  change ⁅p,0⁆+(1:ℝ) • ((n:ℝ) • p)=⁅q,0⁆+(1:ℝ) • ((n:ℝ) • q) at hh
  simp only [lie_zero,one_smul,zero_add] at hh
  exact (smul_right_injective M (by exact_mod_cast (Nat.ne_of_gt hn) : (n:ℝ)≠0)) hh

end RealDeligneDrinfeld.AffineWeight

namespace RealDeligneDrinfeld.BraidCutoff
open DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.TruncatedWords DeligneDrinfeld.LieCutoffFaithful
open scoped TensorProduct
attribute [local instance] LieRing.ofAssociativeRing
abbrev Piece (n : ℕ) := weightPiece (fun _ : Edge => 1) n
 theorem of_mem (a : Edge) : FreeLieAlgebra.of ℝ a∈Piece 1 :=
  Submodule.subset_span (WeightedWord.generator _)
 theorem chord_mem (i j : Fin 4) : chord i j∈Piece 1 := by
  unfold chord
  split_ifs
  · exact of_mem _
  · exact of_mem _
  · exact Submodule.zero_mem _
 theorem piece_lie {n m : ℕ} {a b : BraidFree} (ha : a∈Piece n) (hb : b∈Piece m) : ⁅a,b⁆∈Piece (n+m) := by
  apply Submodule.span_induction (p:=fun a _ => ⁅a,b⁆∈Piece (n+m)) ?_ ?_ ?_ ?_ ha
  · intro a ha
    apply Submodule.span_induction (p:=fun b _ => ⁅a,b⁆∈Piece (n+m)) ?_ ?_ ?_ ?_ hb
    · intro b hb; exact Submodule.subset_span (WeightedWord.bracket ha hb)
    · rw [lie_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
    · intro s b _ hb; rw [lie_smul]; exact Submodule.smul_mem _ s hb
  · rw [zero_lie]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_lie]; exact Submodule.add_mem _ ha hb
  · intro s a _ ha; rw [smul_lie]; exact Submodule.smul_mem _ s ha
 theorem relation_piece {p : BraidFree} (hp : p∈braidRelations) : p∈Piece 2 := by
  rcases hp with ⟨i,j,k,l,_,_,_,_,_,_,rfl⟩|⟨i,j,k,_,_,_,rfl⟩
  · exact piece_lie (n:=1) (m:=1) (chord_mem i j) (chord_mem k l)
  · exact piece_lie (n:=1) (m:=1) (chord_mem i j) ((Piece 1).add_mem (chord_mem i k) (chord_mem j k))

 def affineGenerators (a : Edge) : Module.End ℝ (T4×ℝ) := AffineWeight.homogeneous 1 (projection (FreeLieAlgebra.of ℝ a))
 theorem projection_eq : FreeLieAlgebra.lift ℝ (fun a : Edge => projection (FreeLieAlgebra.of ℝ a))=projection := by
  apply FreeLieAlgebra.hom_ext
  intro a
  exact FreeLieAlgebra.lift_of_apply _ a
 theorem affine_weight {n : ℕ} {p : BraidFree} (hp : p∈Piece n) :
    FreeLieAlgebra.lift ℝ affineGenerators p=AffineWeight.homogeneous n (projection p) := by
  have hh := AffineWeight.weight_rep (fun a : Edge => projection (FreeLieAlgebra.of ℝ a)) hp
  rw [projection_eq] at hh
  exact hh

 def representation (N : ℕ) : Q N →ₐ[ℝ] (DeligneDrinfeld.LieCutoffFaithful.S ℝ N ⊗[ℝ] Module.End ℝ (T4×ℝ)) :=
  RingQuot.liftAlgHom ℝ ⟨DeligneDrinfeld.LieCutoffFaithful.lift N affineGenerators,by
    rintro p q ⟨rfl,hp⟩
    rw [map_zero]
    rcases hp with ⟨p,hp,rfl⟩|hp
    · rw [lift_piece N affineGenerators (relation_piece hp),affine_weight (relation_piece hp),projection_relation hp,map_zero,TensorProduct.tmul_zero]
    · exact lift_above N affineGenerators hp⟩

 theorem representation_quotient (N : ℕ) (p : DeligneDrinfeld.AssociativeElimination.A ℝ Edge) :
    representation N (quotient presentation N p)=DeligneDrinfeld.LieCutoffFaithful.lift N affineGenerators p := by
  simp only [representation,quotient,RingQuot.liftAlgHom_mkAlgHom_apply]

 theorem detect {N n : ℕ} (hn : 0<n) (hN : n≤N) {p : BraidFree} (hp : p∈Piece n)
    (hz : lieMap N (projection p)=0) : projection p=0 := by
  have hh := congrArg (representation N) hz
  change representation N (quotient presentation N (embed p))=representation N 0 at hh
  rw [representation_quotient,map_zero,lift_piece N affineGenerators hp,affine_weight hp] at hh
  have hg := congrArg (DeligneDrinfeld.LieCutoffFaithful.extract N n) hh
  rw [extract_tmul hN,map_zero] at hg
  exact AffineWeight.homogeneous_injective hn (by simpa only [map_zero] using hg)

end RealDeligneDrinfeld.BraidCutoff

section
namespace DeligneDrinfeld.TopDifference
open AssociativeElimination TruncatedWords
variable {R α : Type*} [CommRing R] (P : Set (A R α)) (N : ℕ)
 theorem product_zero {u v : Q P N} (hu : u∈filtration P N N) (hv : v∈filtration P N 1) : u*v=0 := by
  have hh := filtration_mul P N N 1 hu hv
  rwa [filtration_terminal,Submodule.mem_bot] at hh
 theorem reverse_zero {u v : Q P N} (hu : u∈filtration P N 1) (hv : v∈filtration P N N) : u*v=0 := by
  have hh := filtration_mul P N 1 N hu hv
  rwa [Nat.add_comm 1 N,filtration_terminal,Submodule.mem_bot] at hh
 theorem product {a a' b b' : Q P N}
    (ha : a-1∈filtration P N 1) (hb' : b'-1∈filtration P N 1)
    (ha' : a'-a∈filtration P N N) (hb : b'-b∈filtration P N N) :
    a'*b'-a*b=(a'-a)+(b'-b) := by
  have h₁ := product_zero P N ha' hb'
  have h₂ := reverse_zero P N ha hb
  have hh : a'*b'-a*b-((a'-a)+(b'-b))=(a'-a)*(b'-1)+(a-1)*(b'-b) := by
    simp only [sub_mul,mul_sub,mul_one,one_mul]; abel
  apply sub_eq_zero.mp
  rw [hh,h₁,h₂,add_zero]
 theorem normalized_product {a b : Q P N}
    (ha : a-1∈filtration P N 1) (hb : b-1∈filtration P N 1) :
    a*b-1∈filtration P N 1 := by
  have ha0 : a∈filtration P N 0 := by
    obtain ⟨p,rfl⟩ := RingQuot.mkAlgHom_surjective R (relations P N) a
    exact ⟨p,TruncatedFree.all_ge_zero p,rfl⟩
  have hh := filtration_mul P N 0 1 ha0 hb
  convert (filtration P N 1).add_mem hh ha using 1
  simp only [mul_sub,mul_one]; abel
 theorem triple {a a' b b' c c' : Q P N}
    (ha : a-1∈filtration P N 1) (hb : b-1∈filtration P N 1)
    (hb' : b'-1∈filtration P N 1) (hc' : c'-1∈filtration P N 1)
    (hd₁ : a'-a∈filtration P N N) (hd₂ : b'-b∈filtration P N N)
    (hd₃ : c'-c∈filtration P N N) :
    a'*b'*c'-a*b*c=(a'-a)+(b'-b)+(c'-c) := by
  have hh := product P N ha hb' hd₁ hd₂
  have hd : a'*b'-a*b∈filtration P N N := by rw [hh]; exact Submodule.add_mem _ hd₁ hd₂
  rw [product P N (normalized_product P N ha hb) hc' hd hd₃,hh]
end DeligneDrinfeld.TopDifference

namespace RealDeligneDrinfeld.BraidInsertionExp
open DeligneDrinfeld.TruncatedWords
 theorem insert_mem (N : ℕ) (X Y : T4) (hX hY) {n : ℕ} {a : FreeCutoffCategory.Q N}
    (ha : a∈FreeCutoffCategory.F N n) : insert N X Y hX hY a∈BraidCutoff.F N n :=
  DeligneDrinfeld.PresentedSubstitution.subst_mem _ _ _ _ ha
 theorem linear_pentagon_difference (N : ℕ) (u v : FreeCutoffCategory.Q N)
    (hu : u-1∈FreeCutoffCategory.F N 1) (hv : v-1∈FreeCutoffCategory.F N 1)
    (hd : v-u∈FreeCutoffCategory.F N N)
    (hpu : IDE N u*IAD N u=ICE N u*IBC N u*IAB N u)
    (hpv : IDE N v*IAD N v=ICE N v*IBC N v*IAB N v) :
    IDE N (v-u)+IAD N (v-u)=ICE N (v-u)+IBC N (v-u)+IAB N (v-u) := by
  have normal (X Y : T4) (hX hY) (a : FreeCutoffCategory.Q N) (ha : a-1∈FreeCutoffCategory.F N 1) :
      insert N X Y hX hY a-1∈BraidCutoff.F N 1 := by
    simpa only [map_sub,map_one] using insert_mem N X Y hX hY ha
  have diff (X Y : T4) (hX hY) : insert N X Y hX hY v-insert N X Y hX hY u∈BraidCutoff.F N N := by
    simpa only [map_sub] using insert_mem N X Y hX hY hd
  have nd : IDE N u-1∈BraidCutoff.F N 1 := normal _ _ _ _ u hu
  have na : IAD N v-1∈BraidCutoff.F N 1 := normal _ _ _ _ v hv
  have nc : ICE N u-1∈BraidCutoff.F N 1 := normal _ _ _ _ u hu
  have nb : IBC N u-1∈BraidCutoff.F N 1 := normal _ _ _ _ u hu
  have nb' : IBC N v-1∈BraidCutoff.F N 1 := normal _ _ _ _ v hv
  have nab : IAB N v-1∈BraidCutoff.F N 1 := normal _ _ _ _ v hv
  have dd : IDE N v-IDE N u∈BraidCutoff.F N N := diff _ _ _ _
  have da : IAD N v-IAD N u∈BraidCutoff.F N N := diff _ _ _ _
  have dc : ICE N v-ICE N u∈BraidCutoff.F N N := diff _ _ _ _
  have db : IBC N v-IBC N u∈BraidCutoff.F N N := diff _ _ _ _
  have dab : IAB N v-IAB N u∈BraidCutoff.F N N := diff _ _ _ _
  have h₂ := DeligneDrinfeld.TopDifference.product BraidCutoff.presentation N nd na dd da
  have h₃ := DeligneDrinfeld.TopDifference.triple BraidCutoff.presentation N nc nb nb' nab dc db dab
  simp only [map_sub]
  rw [←h₂,←h₃,hpu,hpv]
end RealDeligneDrinfeld.BraidInsertionExp

end

namespace RealDeligneDrinfeld.PentagonDetect
open BraidCutoff BraidInsertionExp
 def value (p : L) : BraidFree :=
  eval (chord 0 1) (chord 1 2+chord 1 3) p+eval (chord 0 2+chord 1 2) (chord 2 3) p-
    (eval (chord 1 2) (chord 2 3) p+eval (chord 0 1+chord 0 2) (chord 1 3+chord 2 3) p+
      eval (chord 0 1) (chord 1 2) p)
 theorem eval_mem {n : ℕ} {p : L} (hp : p∈Ln n) {a b : BraidFree} (ha : a∈Piece 1) (hb : b∈Piece 1) :
    eval a b p∈Piece n := by
  apply WeightBridge.map_mem (eval a b) (fun _ => 1) (fun _ => 1) _ hp
  intro i
  cases i
  · simpa only [eval,FreeLieAlgebra.lift_of_apply,Bool.false_eq_true,↓reduceIte] using ha
  · simpa only [eval,FreeLieAlgebra.lift_of_apply,↓reduceIte] using hb
 theorem homogeneous {n : ℕ} {p : L} (hp : p∈Ln n) : value p∈Piece n := by
  apply (Piece n).sub_mem
  · exact (Piece n).add_mem (eval_mem hp (chord_mem _ _) ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _)))
      (eval_mem hp ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _)) (chord_mem _ _))
  · exact (Piece n).add_mem ((Piece n).add_mem (eval_mem hp (chord_mem _ _) (chord_mem _ _))
      (eval_mem hp ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _)) ((Piece 1).add_mem (chord_mem _ _) (chord_mem _ _))))
      (eval_mem hp (chord_mem _ _) (chord_mem _ _))
 theorem projection_chord (i j : Fin 4) : projection (chord i j)=t i j := rfl
 theorem projection_eval (a b : BraidFree) (p : L) : projection (eval a b p)=eval (projection a) (projection b) p := by
  have he : projection.comp (eval a b)=eval (projection a) (projection b) := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp [eval]
  exact LieHom.congr_fun he p
 theorem detect {n : ℕ} (hn : 0<n) {p : L} (hp : p∈Ln n)
    (he : IDE n (FreeCutoffCategory.j n p)+IAD n (FreeCutoffCategory.j n p)=
      ICE n (FreeCutoffCategory.j n p)+IBC n (FreeCutoffCategory.j n p)+IAB n (FreeCutoffCategory.j n p)) :
    eval (t 0 1) (t 1 2+t 1 3) p+eval (t 0 2+t 1 2) (t 2 3) p=
      eval (t 1 2) (t 2 3) p+eval (t 0 1+t 0 2) (t 1 3+t 2 3) p+eval (t 0 1) (t 1 2) p := by
  have hh : lieMap n (projection (value p))=0 := by
    simp only [value,map_sub,map_add,projection_eval,projection_chord]
    simpa only [sub_eq_zero,IAB,IAD,IDE,IBC,ICE,insert_j,T4Basic.a,T4Basic.b,T4Basic.c,T4Basic.d,T4Basic.e] using he
  have hz := BraidCutoff.detect hn le_rfl (homogeneous hp) hh
  simpa only [value,map_sub,map_add,projection_eval,projection_chord,sub_eq_zero] using hz
end RealDeligneDrinfeld.PentagonDetect

namespace RealDeligneDrinfeld.KZHomogeneous
open DeligneDrinfeld DeligneDrinfeld.AssociativeElimination DeligneDrinfeld.WordGrading
open DeligneDrinfeld.CutoffPrimitiveExtract DeligneDrinfeld.TruncatedWords
open BraidInsertionExp
 theorem value_sum (N : ℕ) : KZComparison.value N=FreeCutoffCategory.j N (∑ i∈Finset.range (N+1),q i) := by
  have hz := quotient_above (∅:Set (A ℝ Bool)) N (residual_above N (N+1) le_rfl)
  rw [map_sub,map_sum,quotient_normal] at hz
  rw [map_sum]
  exact sub_eq_zero.mp hz
 theorem residual_top (N : ℕ) : KZComparison.value N-FreeCutoffCategory.j N (∑ i∈Finset.range N,q i)=
    FreeCutoffCategory.j N (q N) := by
  rw [value_sum,Finset.sum_range_succ,map_add,add_sub_cancel_left]
 theorem coefficient_solution (N : ℕ) : q N∈W := by
  induction N using Nat.strong_induction_on with | h N ih =>
    by_cases hN : N≤2
    · rw [q_low hN]; exact Submodule.zero_mem _
    have hN' : 2<N := by omega
    let ns : Fin N → ℕ := fun (i : Fin N) => if 2 < i.val then i.val else 3
    have hn : ∀ i,2<ns i := by intro i; dsimp [ns]; split_ifs <;> omega
    have hqn : ∀ i : Fin N,q i.val∈Ln (ns i) := by
      intro i
      dsimp [ns]
      split_ifs with hi
      · exact q_homogeneous _
      · rw [q_low (by omega)]; exact Submodule.zero_mem _
    have hq : ∀ i : Fin N,q i.val∈W := fun i => ih i.val i.isLt
    have hsum : (∑ i : Fin N,q i.val)=∑ i∈Finset.range N,q i := Fin.sum_univ_eq_sum_range q N
    let g := BraidInsertionSum.free N Finset.univ (fun i : Fin N => q i.val) ns hqn
    let u := CategoryExp.act g 0 1 (KZComparison.positive N)
    have hd : KZComparison.value N-FreeCutoffCategory.j N (∑ i : Fin N,q i.val)=FreeCutoffCategory.j N (q N) := by
      rw [hsum,residual_top]
    have hj := FreeCutoffCategory.j_mem (N:=N) (q_homogeneous N)
    have hex := KZLogDifference.exponential N Finset.univ (fun i : Fin N => q i.val) ns hqn hn N (by rw [hd]; exact hj)
    change _ ∈filtration (∅:Set (A ℝ Bool)) N (N+1) at hex
    rw [filtration_terminal,Submodule.mem_bot,hd] at hex
    have hdiff : (KZComparison.negative N:FreeCutoffCategory.Q N)-u=FreeCutoffCategory.j N (q N) := sub_eq_zero.mp hex
    have hp := BraidInsertionSum.pentagon N Finset.univ (fun i : Fin N => q i.val) ns hq hqn hn _ (KZBraidPentagon.positive N)
    have hu : u-1∈FreeCutoffCategory.F N 1 := by
      have hr := BraidInsertionSum.free_raises N Finset.univ (fun i : Fin N => q i.val) ns hqn hn 0 1
      have hh := CategoryExp.unit_leading (CutoffCategory.filtration ∅ N) (g.D 0 1) 1 hr (by omega)
        (filtration_one ∅ N) (KZComparison.positive_weight N)
      have hd1 := hr 0 1 (filtration_one ∅ N)
      have hh' := filtration_antitone (∅:Set (A ℝ Bool)) N (by omega : 1≤1+1) hh
      have hz := (FreeCutoffCategory.F N 1).add_mem ((FreeCutoffCategory.F N 1).add_mem hh' hd1) (KZComparison.positive_weight N)
      convert hz using 1
      dsimp [u,CategoryExp.act]
      abel
    have hh := linear_pentagon_difference N u (KZComparison.negative N) hu (KZComparison.negative_weight N)
      (by rw [hdiff]; exact hj) hp (KZBraidPentagon.negative N)
    rw [hdiff] at hh
    exact ⟨anti N,cyclic N,PentagonDetect.detect (by omega) (q_homogeneous N) hh⟩
end RealDeligneDrinfeld.KZHomogeneous

end

end OAI

end

section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

namespace RationalDescent
open scoped TensorProduct
variable {K V E : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup E] [Module K E]

theorem factor_of_kernel (f : V →ₗ[K] E) (l : V →ₗ[K] K) (h : f.ker≤l.ker) :
    ∃ g : E →ₗ[K] K,g.comp f=l := by
  let r : f.range →ₗ[K] K := ((f.ker).liftQ l h).comp f.quotKerEquivRange.symm.toLinearMap
  obtain ⟨g,hg⟩ := r.exists_extend
  refine ⟨g,?_⟩
  ext v
  have hh := LinearMap.congr_fun hg (f.rangeRestrict v)
  change g (f v)=r (f.rangeRestrict v) at hh
  change g (f v)=l v
  rw [hh]
  simp only [r,LinearMap.comp_apply,LinearEquiv.coe_coe]
  exact congrArg (f.ker.liftQ l h) (f.quotKerEquivRange.symm_apply_apply (f.ker.mkQ v))

theorem nonvanishing {S : Type*} [AddCommGroup S] [Module K S]
    (f : V →ₗ[K] E) (l : V →ₗ[K] K)
    (u : S ⊗[K] V) (hu : f.lTensor S u=0) (hl : l.lTensor S u≠0) :
    ∃ v : V,f v=0 ∧ l v≠0 := by
  by_contra hn
  have hk : f.ker≤l.ker := by
    intro v hv
    by_contra hv'
    exact hn ⟨v,hv,hv'⟩
  obtain ⟨g,hg⟩ := factor_of_kernel f l hk
  apply hl
  rw [←hg,LinearMap.lTensor_comp,LinearMap.comp_apply,hu,map_zero]

end RationalDescent

namespace RationalScalar

section
open scoped TensorProduct
open AssociativeElimination UniversalEmbedding
attribute [local instance] LieRing.ofAssociativeRing
variable {M N : Type*} [LieRing M] [LieAlgebra ℚ M] [LieRing N] [LieAlgebra ℚ N]
abbrev T (M : Type*) [AddCommGroup M] [Module ℚ M] := ℝ ⊗[ℚ] M
 def one : M →ₗ⁅ℚ⁆ T M where
  toLinearMap := TensorProduct.mk ℚ ℝ M 1
  map_lie' := by
    intro a b
    change 1 ⊗ₜ[ℚ] ⁅a,b⁆=⁅(1:ℝ) ⊗ₜ[ℚ] a,(1:ℝ) ⊗ₜ[ℚ] b⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul,one_mul]
 def base (f : M →ₗ⁅ℚ⁆ N) : T M →ₗ⁅ℝ⁆ T N where
  toLinearMap := f.toLinearMap.baseChange ℝ
  map_lie' := by
    intro a b
    change (f.toLinearMap.baseChange ℝ) ⁅a,b⁆=⁅(f.toLinearMap.baseChange ℝ) a,(f.toLinearMap.baseChange ℝ) b⁆
    induction a using TensorProduct.induction_on with
    | zero => first | rfl | exact Submodule.zero_mem _ | simp
    | tmul s a =>
      induction b using TensorProduct.induction_on with
      | zero => first | rfl | exact Submodule.zero_mem _ | simp
      | tmul t b =>
        simp only [LieAlgebra.ExtendScalars.bracket_tmul,LinearMap.baseChange_tmul]
        change (s*t) ⊗ₜ[ℚ] f ⁅a,b⁆=(s*t) ⊗ₜ[ℚ] ⁅f a,f b⁆
        rw [LieHom.map_lie]
      | add a b ha hb => simp only [lie_add,map_add,ha,hb]
    | add a b ha hb => simp only [add_lie,map_add,ha,hb]
 @[simp] theorem base_tmul (f : M →ₗ⁅ℚ⁆ N) (s : ℝ) (p : M) : base f (s ⊗ₜ[ℚ] p)=s ⊗ₜ[ℚ] f p := rfl
variable {α : Type*}
 def free : FreeLieAlgebra ℝ α →ₗ⁅ℝ⁆ T (FreeLieAlgebra ℚ α) :=
  FreeLieAlgebra.lift ℝ (fun a => 1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ a)
 @[simp] theorem free_of (a : α) : free (FreeLieAlgebra.of ℝ a)=1 ⊗ₜ[ℚ] FreeLieAlgebra.of ℚ a := FreeLieAlgebra.lift_of_apply _ _
 theorem free_tree (t : UniversalEmbedding.Tree α) : free (t.eval : FreeLieAlgebra ℝ α)=1 ⊗ₜ[ℚ] (t.eval : FreeLieAlgebra ℚ α) := by
  induction t with
  | leaf a => exact free_of a
  | node t u ht hu => simp only [Tree.eval,LieHom.map_lie,ht,hu,LieAlgebra.ExtendScalars.bracket_tmul,one_mul]
 theorem cast_tree {S : Type*} [CommRing S] (t : UniversalEmbedding.Tree α) :
    IntegralBaseChange.lie (t.eval : FreeLieAlgebra ℤ α)=(t.eval : FreeLieAlgebra S α) := by
  induction t with
  | leaf a => exact IntegralBaseChange.lie_of a
  | node t u ht hu => simp only [Tree.eval,LieHom.map_lie,ht,hu]
 theorem tree_coefficient (t : UniversalEmbedding.Tree α) (w : FreeMonoid α) :
    ((embed (t.eval : FreeLieAlgebra ℚ α)).coeff w:ℝ)=(embed (t.eval : FreeLieAlgebra ℝ α)).coeff w := by
  rw [←cast_tree (S:=ℚ) t,←cast_tree (S:=ℝ) t,IntegralBaseChange.embed_lie,IntegralBaseChange.embed_lie,
    IntegralBaseChange.words_coeff,IntegralBaseChange.words_coeff]
  simp
 def coefficient (w : FreeMonoid α) : FreeLieAlgebra ℚ α →ₗ[ℚ] ℚ :=
  (Finsupp.lapply w).comp ((MonoidAlgebra.coeffLinearEquiv ℚ).toLinearMap.comp embed.toLinearMap)
 def realCoefficient (w : FreeMonoid α) : T (FreeLieAlgebra ℚ α) →ₗ[ℝ] ℝ :=
  TensorProduct.AlgebraTensorModule.lift (LinearMap.smulRight (LinearMap.id : ℝ →ₗ[ℝ] ℝ)
    ((Algebra.linearMap ℚ ℝ).comp (coefficient w)))
 @[simp] theorem realCoefficient_tmul (w : FreeMonoid α) (s : ℝ) (p : FreeLieAlgebra ℚ α) :
    realCoefficient w (s ⊗ₜ[ℚ] p)=s*(coefficient w p:ℝ) := rfl
 theorem coefficient_free {wt : α → ℕ} {n : ℕ} {p : FreeLieAlgebra ℝ α}
    (hp : p∈RealDeligneDrinfeld.weightPiece wt n) (w : FreeMonoid α) :
    realCoefficient w (free p)=(embed p).coeff w := by
  rw [RealDeligneDrinfeld.WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,_ht,rfl⟩ := hp
    rw [free_tree,realCoefficient_tmul,one_mul]
    exact tree_coefficient t w
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,MonoidAlgebra.coeff_add,Finsupp.add_apply]
  | smul s p _ hp => simp only [map_smul,hp,MonoidAlgebra.coeff_smul,Finsupp.smul_apply]
 theorem realCoefficient_tensor (w : FreeMonoid α) (u : T (FreeLieAlgebra ℚ α)) :
    realCoefficient w u=TensorProduct.rid ℚ ℝ ((coefficient w).lTensor ℝ u) := by
  induction u using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | tmul s p =>
    simp only [realCoefficient_tmul,LinearMap.lTensor_tmul,TensorProduct.rid_tmul]
    change s*(coefficient w p:ℝ)=(coefficient w p:ℝ)*s
    exact mul_comm _ _
  | add a b ha hb => simp only [map_add,ha,hb]
end

open scoped TensorProduct
 def realT4 : RealDeligneDrinfeld.T4 →ₗ⁅ℝ⁆ T T4 :=
  RealDeligneDrinfeld.T4Universal.lift (fun i j => one (t i j))
    (fun i j => congrArg one (t_comm i j)) (fun i => by rw [t_self,map_zero])
    (fun i j k l hij hik hil hjk hjl hkl => by rw [←LieHom.map_lie,t_disjoint i j k l hij hik hil hjk hjl hkl,map_zero])
    (fun i j k hij hik hjk => by rw [←map_add,←LieHom.map_lie,t_three i j k hij hik hjk,map_zero])
 @[simp] theorem realT4_t (i j : Fin 4) : realT4 (RealDeligneDrinfeld.t i j)=one (t i j) :=
  RealDeligneDrinfeld.T4Universal.lift_t _ _ _ _ _ _ _
 theorem eval_natural {M : Type*} [LieRing M] [LieAlgebra ℚ M]
    {P : Type*} [LieRing P] [LieAlgebra ℝ P] (g : P →ₗ⁅ℝ⁆ T M)
    (a b : M) (a' b' : P) (ha : g a'=one a) (hb : g b'=one b) (p : RealDeligneDrinfeld.L) :
    base (eval a b) (free p)=g (RealDeligneDrinfeld.eval a' b' p) := by
  have hh : (base (eval a b)).comp free=g.comp (RealDeligneDrinfeld.eval a' b') := by
    apply FreeLieAlgebra.hom_ext
    intro i
    cases i <;> simp only [LieHom.comp_apply,free_of,base_tmul,eval,RealDeligneDrinfeld.eval,FreeLieAlgebra.lift_of_apply,Bool.false_eq_true,ite_false,ite_true] <;> first | exact ha.symm | exact hb.symm
  exact DFunLike.congr_fun hh p
 def antiMap : L →ₗ[ℚ] L := LinearMap.id+(eval y x).toLinearMap
 def cyclicMap : L →ₗ[ℚ] L := LinearMap.id+(eval y (-x-y)).toLinearMap+(eval (-x-y) x).toLinearMap
 def pentagonMap : L →ₗ[ℚ] T4 :=
  (eval (t 0 1) (t 1 2+t 1 3)).toLinearMap+(eval (t 0 2+t 1 2) (t 2 3)).toLinearMap-
  ((eval (t 1 2) (t 2 3)).toLinearMap+(eval (t 0 1+t 0 2) (t 1 3+t 2 3)).toLinearMap+(eval (t 0 1) (t 1 2)).toLinearMap)
 theorem tensor_add {A B : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    (f g : A →ₗ[ℚ] B) (u : T A) : (f+g).lTensor ℝ u=f.lTensor ℝ u+g.lTensor ℝ u := by
  induction u using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | tmul s p => simp
  | add a b ha hb => simp only [map_add,ha,hb]; abel
 theorem tensor_sub {A B : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    (f g : A →ₗ[ℚ] B) (u : T A) : (f-g).lTensor ℝ u=f.lTensor ℝ u-g.lTensor ℝ u := by
  induction u using TensorProduct.induction_on with
  | zero => first | rfl | exact Submodule.zero_mem _ | simp
  | tmul s p => simp
  | add a b ha hb => simp only [map_add,ha,hb]; abel
 theorem tensor_id (u : T L) : (LinearMap.id : L →ₗ[ℚ] L).lTensor ℝ u=u := by simp
 theorem eval_tensor {M : Type*} [LieRing M] [LieAlgebra ℚ M] (a b : M) (u : T L) :
    (eval a b).toLinearMap.lTensor ℝ u=base (eval a b) u := rfl
 @[simp] theorem free_x : free RealDeligneDrinfeld.x=one x := free_of false
 @[simp] theorem free_y : free RealDeligneDrinfeld.y=one y := free_of true
 theorem equations {p : RealDeligneDrinfeld.L} (hp : p∈RealDeligneDrinfeld.W) :
    antiMap.lTensor ℝ (free p)=0 ∧ cyclicMap.lTensor ℝ (free p)=0 ∧ pentagonMap.lTensor ℝ (free p)=0 := by
  rcases hp with ⟨h1,h2,h3⟩
  constructor
  · rw [antiMap,tensor_add,tensor_id,eval_tensor,eval_natural free y x _ _ free_y free_x,←map_add,h1,map_zero]
  constructor
  · have hz : free (-RealDeligneDrinfeld.x-RealDeligneDrinfeld.y)=one (-x-y) := by simp
    rw [cyclicMap,tensor_add,tensor_add,tensor_id,eval_tensor,eval_tensor,
      eval_natural free y (-x-y) _ _ free_y hz,eval_natural free (-x-y) x _ _ hz free_x,←map_add,←map_add,h2,map_zero]
  · rw [pentagonMap,tensor_sub,tensor_add,tensor_add,tensor_add]
    simp only [eval_tensor]
    have hsum (i j k l : Fin 4) : realT4 (RealDeligneDrinfeld.t i j+RealDeligneDrinfeld.t k l)=one (t i j+t k l) := by simp only [map_add,realT4_t]
    rw [eval_natural realT4 _ _ _ _ (realT4_t 0 1) (hsum 1 2 1 3),
      eval_natural realT4 _ _ _ _ (hsum 0 2 1 2) (realT4_t 2 3),
      eval_natural realT4 _ _ _ _ (realT4_t 1 2) (realT4_t 2 3),
      eval_natural realT4 _ _ _ _ (hsum 0 1 0 2) (hsum 1 3 2 3),
      eval_natural realT4 _ _ _ _ (realT4_t 0 1) (realT4_t 1 2)]
    rw [←map_add,←map_add,←map_add,h3,sub_self]

 theorem homogeneous_tensor {n : ℕ} {p : RealDeligneDrinfeld.L} (hp : p∈RealDeligneDrinfeld.Ln n) :
    (Ln n).mkQ.lTensor ℝ (free p)=0 := by
  change p∈RealDeligneDrinfeld.weightPiece (fun _ => 1) n at hp
  rw [RealDeligneDrinfeld.WeightBridge.piece_eq] at hp
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨t,ht,rfl⟩ := hp
    have hm : (t.eval : L)∈Ln n := by
      change t.eval∈weightPiece (fun _ => 1) n
      rw [LieGrading.weightPiece_eq]
      exact Submodule.subset_span ⟨t,ht,rfl⟩
    rw [free_tree,LinearMap.lTensor_tmul]
    have hz : (Ln n).mkQ (t.eval : L)=0 := (Submodule.Quotient.mk_eq_zero _).mpr hm
    rw [hz,TensorProduct.tmul_zero]
  | zero => simp
  | add p q _ _ hp hq => simp only [map_add,hp,hq,add_zero]
  | smul s p _ hp =>
    rw [map_smul]
    change ((Ln n).mkQ.baseChange ℝ) (s • free p)=0
    rw [map_smul]
    change s • ((Ln n).mkQ.lTensor ℝ (free p))=0
    rw [hp,smul_zero]
 theorem tensor_prod {A B C : Type*} [AddCommGroup A] [Module ℚ A] [AddCommGroup B] [Module ℚ B]
    [AddCommGroup C] [Module ℚ C] (f : A →ₗ[ℚ] B) (g : A →ₗ[ℚ] C) (u : T A)
    (hf : f.lTensor ℝ u=0) (hg : g.lTensor ℝ u=0) : (f.prod g).lTensor ℝ u=0 := by
  have hh : TensorProduct.prodRight ℚ ℝ ℝ B C ((f.prod g).lTensor ℝ u)=(f.lTensor ℝ u,g.lTensor ℝ u) := by
    clear hf hg
    induction u using TensorProduct.induction_on with
    | zero => first | rfl | exact Submodule.zero_mem _ | simp
    | tmul s a => simp
    | add a b ha hb => simp only [map_add,ha,hb,Prod.mk_add_mk]
  apply (TensorProduct.prodRight ℚ ℝ ℝ B C).injective
  rw [hh,hf,hg,map_zero]; rfl
 def system (n : ℕ) : L →ₗ[ℚ] (L ⧸ Ln n) × L × L × T4 :=
  (Ln n).mkQ.prod (antiMap.prod (cyclicMap.prod pentagonMap))
 theorem descend {n : ℕ} {p : RealDeligneDrinfeld.L} (hp : p∈RealDeligneDrinfeld.W)
    (hpn : p∈RealDeligneDrinfeld.Ln n) (w : FreeMonoid Bool)
    (hc : (AssociativeElimination.embed p).coeff w≠0) :
    ∃ q : L,q∈Wn n ∧ (AssociativeElimination.embed q).coeff w≠0 := by
  have hs : (system n).lTensor ℝ (free p)=0 := by
    obtain ⟨h1,h2,h3⟩ := equations hp
    exact tensor_prod _ _ _ (homogeneous_tensor hpn) (tensor_prod _ _ _ h1 (tensor_prod _ _ _ h2 h3))
  have hn : (coefficient w).lTensor ℝ (free p)≠0 := by
    intro he
    apply hc
    rw [←coefficient_free hpn w,realCoefficient_tensor,he,map_zero]
  obtain ⟨q,hq,hc⟩ := RationalDescent.nonvanishing (system n) (coefficient w) (free p) hs hn
  have hh : (Ln n).mkQ q=0 ∧ antiMap q=0 ∧ cyclicMap q=0 ∧ pentagonMap q=0 := by
    change ((Ln n).mkQ q,antiMap q,cyclicMap q,pentagonMap q)=(0,0,0,0) at hq
    simpa only [Prod.mk.injEq] using hq
  refine ⟨q,⟨⟨hh.2.1,hh.2.2.1,?_⟩,(Submodule.Quotient.mk_eq_zero _).mp hh.1⟩,hc⟩
  exact sub_eq_zero.mp hh.2.2.2
end RationalScalar

end DeligneDrinfeld

end

end OAI

end



section

namespace OAI

noncomputable section

namespace DeligneDrinfeld

section
end

section

end

open AssociativeElimination WordGrading
 theorem real_odd_nonzero (k : ℕ) :
    (embed (RealDeligneDrinfeld.KZHomogeneous.q (2*k+3))).coeff (GenericIhara.depthOneWord (2*k+2))≠0 := by
  rw [RealDeligneDrinfeld.KZHomogeneous.q_embed_any (2*k+3) (2*k+3) le_rfl]
  change (piece (fun _ => 1) (2*k+3) _).coeff _≠0
  rw [piece,project_coeff,if_pos (by rw [CutoffDepth.length_depthOne])]
  exact KZComparison.odd_value_nonzero k
 theorem odd_solution_oai (k : ℕ) : ∃ q : L,q∈Wn (oddWeight k) ∧
    (embed q).coeff (GenericIhara.depthOneWord (oddWeight k-1))≠0 := by
  have hh := RationalScalar.descend (RealDeligneDrinfeld.KZHomogeneous.coefficient_solution (2*k+3))
    (RealDeligneDrinfeld.KZHomogeneous.q_homogeneous (2*k+3))
    (GenericIhara.depthOneWord (2*k+2)) (real_odd_nonzero k)
  simpa only [oddWeight,show 2*k+3-1=2*k+2 by omega] using hh

end DeligneDrinfeld

end

end OAI

end

section
open OAI.DeligneDrinfeld

attribute [local instance] LieRing.ofAssociativeRing in
theorem solution (k : ℕ) :
    ∃ q : L, q ∈ Wn (oddWeight k) ∧
      (FreeLieAlgebra.lift ℚ
          (fun a : Bool => (MonoidAlgebra.single (FreeMonoid.of a) 1 :
            MonoidAlgebra ℚ (FreeMonoid Bool))) q).coeff
        (FreeMonoid.of false ^ (2 * k + 2) * FreeMonoid.of true) ≠ 0 := by
  obtain ⟨q, hq, hc⟩ := OAI.DeligneDrinfeld.odd_solution_oai k
  have e : oddWeight k - 1 = 2 * k + 2 := by simp [oddWeight]
  rw [e] at hc
  exact ⟨q, hq, hc⟩

end
