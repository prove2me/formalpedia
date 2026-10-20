-- Prove2me | solution 1 for OAI.SingleFold.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T19:35:09.400492+00:00
-- url     : https://prove2.me/submissions/a48022de-035b-4e06-a1e1-11831420d39e

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/SingleFold/Main.lean:L21-L25
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.SingleFold.main.
-- The source declaration is kept inside its namespace next to the proof-only helpers it needs;
-- `theorem solution` restates the platform stub (Theorems.Thm_OAI_SingleFold_main) verbatim and is proved by it.
import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticGrowth
import Definitions.Def_OAI_NumberTheory_SingleFold_Pell
import Definitions.Def_OAI_NumberTheory_SingleFold_Power
import Definitions.Def_OAI_NumberTheory_SingleFold_Binary
import Definitions.Def_OAI_NumberTheory_SingleFold_Packed
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterBounds
import Definitions.Def_OAI_NumberTheory_SingleFold_CounterCompilation
import Definitions.Def_OAI_NumberTheory_SingleFold_MacroMachine
import Definitions.Def_OAI_NumberTheory_SingleFold_TuringSimulation
import Definitions.Def_OAI_NumberTheory_SingleFold_RecursiveEnumeration
import Theorems.Thm_OAI_SingleFold_Binary_choose_digit
import Theorems.Thm_OAI_SingleFold_Binary_choose_odd_iff
import Theorems.Thm_OAI_SingleFold_Binary_extract_unique
import Theorems.Thm_OAI_SingleFold_Compiler_ScalarSF_sub
import Theorems.Thm_OAI_SingleFold_Compiler_export_polynomial
import Theorems.Thm_OAI_SingleFold_Counter_System_haltsAt
import Theorems.Thm_OAI_SingleFold_Counter_eval_dom_iff_halts
import Theorems.Thm_OAI_SingleFold_Counter_system_unique
import Theorems.Thm_OAI_SingleFold_Counter_trace_system
import Theorems.Thm_OAI_SingleFold_CurveRank_representatives_card
import Theorems.Thm_OAI_SingleFold_EllipticModel_W_index
import Theorems.Thm_OAI_SingleFold_GrowthCompilation_graph_sf
import Theorems.Thm_OAI_SingleFold_GrowthEstimate_bracket_unique
import Theorems.Thm_OAI_SingleFold_GrowthEstimate_eventual_output
import Theorems.Thm_OAI_SingleFold_GrowthEstimate_sequence_strict
import Theorems.Thm_OAI_SingleFold_HeightWindow_square_window
import Theorems.Thm_OAI_SingleFold_Packed_unique_scale
import Theorems.Thm_OAI_SingleFold_PellSystem_quotient_sound
import Theorems.Thm_OAI_SingleFold_PowerEstimate_input_bounds
import Theorems.Thm_OAI_SingleFold_PowerSystem_complete
import Theorems.Thm_OAI_SingleFold_PowerSystem_pinned
import Theorems.Thm_OAI_SingleFold_TM2Macro_stepAux_reaches

-- ---- from OAI.NumberTheory.SingleFold.RationalCodes ----
namespace OAI

namespace SingleFold

namespace RationalCode

end RationalCode
end SingleFold

namespace SingleFold.Compiler.SF
variable {α β : Type} {R S : (α → ℕ) → Prop}

theorem congr (h : SF R) (he : ∀ x, R x ↔ S x) : SF S := by
  obtain ⟨r⟩ := h
  exact ⟨r.congr he⟩
theorem and (hR : SF R) (hS : SF S) : SF (fun x => R x ∧ S x) := by
  obtain ⟨r⟩ := hR; obtain ⟨s⟩ := hS
  exact ⟨r.and s⟩
theorem reindex (hR : SF R) (f : α → β) : SF (fun x => R (x ∘ f)) := by
  obtain ⟨r⟩ := hR; exact ⟨r.reindex f⟩
theorem all [Finite β] {R : β → (α → ℕ) → Prop} (hr : ∀ i, SF (R i)) : SF (fun x => ∀ i, R i x) :=
  ⟨Representation.all R (fun i => Classical.choice (hr i))⟩
theorem eq (p q : Poly α) : SF (fun x => p x=q x) := ⟨Representation.eq p q⟩
theorem le (p q : Poly α) : SF (fun x => p x≤q x) := ⟨Representation.le p q⟩
theorem lt (p q : Poly α) : SF (fun x => p x<q x) := ⟨Representation.lt p q⟩
theorem ex {R : (α ⊕ β → ℕ) → Prop} [Finite β] (hr : SF R)
    (hu : ∀ x y y', R (Sum.elim x y) → R (Sum.elim x y') → y=y') :
    SF (fun x => ∃ y, R (Sum.elim x y)) := by
  obtain ⟨r⟩ := hr; exact ⟨r.ex hu⟩
end SingleFold.Compiler.SF

namespace SingleFold.RationalCompiler
open Compiler

namespace FractionPoly
variable {α : Type}
end FractionPoly

namespace Expr
variable {α : Type}
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.Compiler

namespace Semi
variable {α β : Type} {R S : (α → ℕ) → Prop}
end Semi
end SingleFold.Compiler

namespace SingleFold.RationalCompiler
open Compiler

namespace Expr
variable {α β : Type}
end Expr
end SingleFold.RationalCompiler

namespace SingleFold.RationalCode
end SingleFold.RationalCode

end OAI

-- ---- from OAI.NumberTheory.SingleFold.FunctionalCompiler ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Compiler

namespace MapSF
variable {α β γ δ : Type}
lemma congr {f g : (α → ℕ) → (β → ℕ)} (hf : MapSF f) (hfg : ∀ z, f z=g z) : MapSF g :=
  SF.congr hf (by intro z; rw [hfg])
lemma proj (i : β → α) [Finite β] : MapSF (fun z => z ∘ i) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.proj (Sum.inl (i j))))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=z (Sum.inl (i j))) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma const (b : β → ℕ) [Finite β] : MapSF (fun _ : α → ℕ => b) := by
  have h := SF.all (fun j : β => SF.eq (Poly.proj (Sum.inr j : α⊕β)) (Poly.const (b j)))
  refine h.congr ?_
  intro z
  change (∀ j, (z (Sum.inr j):ℤ)=(b j:ℤ)) ↔ _
  simp only [Int.natCast_inj]
  exact ⟨fun h => funext h,fun h j => congrFun h j⟩
lemma comp {f : (α → ℕ) → (β → ℕ)} {g : (β → ℕ) → (γ → ℕ)} [Finite β]
    (hg : MapSF g) (hf : MapSF f) : MapSF (fun z => g (f z)) := by
  have h := (SF.reindex hf (Sum.elim (Sum.inl ∘ Sum.inl) Sum.inr)).and
    (SF.reindex hg (Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)))
  have hu : ∀ (z : α⊕γ → ℕ) (x y : β → ℕ),
      (x=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g x) →
      (y=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g y) → x=y := by
    intro z x y hx hy; exact hx.1.trans hy.1.symm
  refine (h.ex hu).congr ?_
  intro z
  change (∃ x, x=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr=g x) ↔ _
  simp only [exists_eq_left]
lemma pair {f : (α → ℕ) → (β → ℕ)} {g : (α → ℕ) → (γ → ℕ)}
    (hf : MapSF f) (hg : MapSF g) : MapSF (fun z => Sum.elim (f z) (g z)) := by
  have h := (SF.reindex hf (Sum.map id Sum.inl)).and (SF.reindex hg (Sum.map id Sum.inr))
  refine h.congr ?_
  intro z
  change (z ∘ Sum.inr ∘ Sum.inl=f (z ∘ Sum.inl) ∧ z ∘ Sum.inr ∘ Sum.inr=g (z ∘ Sum.inl)) ↔ _
  constructor
  · rintro ⟨h₁,h₂⟩; funext j; cases j with
    | inl j => exact congrFun h₁ j
    | inr j => exact congrFun h₂ j
  · intro h
    exact ⟨congrArg (fun z => z ∘ Sum.inl) h,congrArg (fun z => z ∘ Sum.inr) h⟩
lemma all [Finite δ] {f : δ → (α → ℕ) → (β → ℕ)} (hf : ∀ d, MapSF (f d)) :
    MapSF (fun z (v : δ×β) => f v.1 z v.2) := by
  have h := SF.all (fun d => SF.reindex (hf d) (Sum.map id (fun j => (d,j))))
  refine h.congr ?_
  intro z
  constructor
  · intro hh; funext ⟨d,j⟩; exact congrFun (hh d) j
  · intro hh d; funext j; exact congrFun hh (d,j)
lemma pullback {f : (α → ℕ) → (β → ℕ)} [Finite β] (hf : MapSF f)
    {R : (β → ℕ) → Prop} (hR : SF R) : SF (fun z => R (f z)) := by
  have h := hf.and (hR.reindex Sum.inr)
  refine (h.ex (fun z x y hx hy => hx.1.trans hy.1.symm)).congr ?_
  intro z
  change (∃ x, x=f z ∧ R x) ↔ _
  simp only [exists_eq_left]
end MapSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
namespace PointSF
variable {α β : Type} {f g : (α → ℕ) → E.Point}
end PointSF
end SingleFold.PointCompiler

namespace SingleFold.Compiler
namespace ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
lemma const (n : ℕ) : ScalarSF (fun _ : α → ℕ => n) := MapSF.const _
lemma proj (i : α) : ScalarSF (fun z => z i) := MapSF.proj (fun _ => i)
lemma poly {f : (α → ℕ) → ℕ} (p : Poly α) (hp : ∀ z, p z=(f z:ℤ)) : ScalarSF f := by
  have h := SF.eq (Poly.proj (Sum.inr () : α⊕Unit)) (p.map Sum.inl)
  refine h.congr ?_
  intro z
  change (z (Sum.inr ()):ℤ)=p (z ∘ Sum.inl) ↔ _
  rw [hp,Int.natCast_inj]
  exact ⟨fun hh => funext (fun j => by cases j; exact hh),fun hh => congrFun hh ()⟩
lemma add (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z+g z) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => z (.inl ())+z (.inr ())) :=
    poly (Poly.proj (.inl ())+Poly.proj (.inr ())) (by intro z; simp)
  exact MapSF.comp h (MapSF.pair hf hg)
lemma mul (hf : ScalarSF f) (hg : ScalarSF g) : ScalarSF (fun z => f z*g z) := by
  have h : ScalarSF (fun z : Unit⊕Unit → ℕ => z (.inl ())*z (.inr ())) :=
    poly (Poly.proj (.inl ())*Poly.proj (.inr ())) (by intro z; simp)
  exact MapSF.comp h (MapSF.pair hf hg)
lemma pow (hf : ScalarSF f) (n : ℕ) : ScalarSF (fun z => f z^n) := by
  have h : ScalarSF (fun z : Unit → ℕ => z ()^n) :=
    poly (Poly.proj ()^n) (by
      intro z
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ,Poly.mul_apply,ih,Poly.proj_apply,Nat.cast_pow,←pow_succ,Nat.cast_pow])
  exact MapSF.comp h hf
lemma le (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z≤g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.le (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)≤(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
lemma lt (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z<g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.lt (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)<(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
lemma eq (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z => f z=g z) := by
  have h := (MapSF.pair hf hg).pullback (SF.eq (Poly.proj (.inl ())) (Poly.proj (.inr ())))
  refine h.congr ?_
  intro z
  change (f z:ℤ)=(g z:ℤ) ↔ _
  exact_mod_cast Iff.rfl
end ScalarSF
end SingleFold.Compiler

namespace SingleFold.PointCompiler
open Compiler RationalCompiler
namespace PointSF
variable {α : Type} {f g : (α → ℕ) → E.Point}
end PointSF
end SingleFold.PointCompiler

end OAI

-- ---- from OAI.NumberTheory.SingleFold.QuadraticHeight ----
namespace OAI

namespace SingleFold.QuadraticLimit

universe u

open Filter Topology

variable {A : Type u} [AddCommGroup A]

variable (h : A → ℝ) (C : ℝ)
variable (hzero : h 0 = 0)
variable (hpara : ∀ P Q, |h (P+Q)+h (P-Q)-2*(h P+h Q)| ≤ C)

end SingleFold.QuadraticLimit

namespace SingleFold.CurveHeight

open WeierstrassCurve.Affine.Point
open Filter Topology

lemma naiveHeight_some {x y : ℚ} (h : E.Nonsingular x y) :
    naiveHeight (some x y h) = Real.log (max x.num.natAbs x.den : ℕ) := by
  rw [naiveHeight, xRep_some, ← Height.logHeight₁_eq_logHeight, Rat.logHeight₁_eq_log_max]

theorem canonicalHeight_pos {P : E.Point} (hP : ¬IsOfFinAddOrder P) :
    0 < canonicalHeight P := by
  by_contra hn
  have hz : canonicalHeight P = 0 := le_antisymm (le_of_not_gt hn) (canonicalHeight_nonneg P)
  obtain ⟨c,hc,hbound⟩ := uniform_height
  have hm (n : ℕ) : naiveHeight (n • P) ≤ c := by
    have hh := hbound (n • P)
    rw [canonicalHeight_nsmul, hz, mul_zero, mul_zero, sub_zero] at hh
    exact (le_abs_self _).trans hh
  have hi : Function.Injective (fun n : ℕ => n • P) :=
    (injective_nsmul_iff_not_isOfFinAddOrder).mpr hP
  exact (Set.infinite_of_injective_forall_mem hi hm) (Northcott.finite_le c)

end SingleFold.CurveHeight

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Rank ----
namespace OAI

namespace SingleFold.AbstractRank

universe u v w

variable (A : Type u) [AddCommGroup A]

lemma index_le_of_cover (F : Finset A) (hF : ∀ P, ∃ R ∈ F, ∃ Q, P=R+(2:ℕ) • Q) :
    (doubleRange A).index ≤ F.card := by
  have hs : Function.Surjective (fun R : F => (QuotientAddGroup.mk R.val : A ⧸ doubleRange A)) := by
    intro x
    obtain ⟨P,rfl⟩ := QuotientAddGroup.mk_surjective x
    obtain ⟨R,hR,Q,hQ⟩ := hF P
    refine ⟨⟨R,hR⟩,?_⟩
    apply QuotientAddGroup.eq.mpr
    change -R+P ∈ doubleRange A
    refine ⟨Q,?_⟩
    simp only [nsmulAddMonoidHom_apply]
    rw [hQ]
    abel
  simpa [AddSubgroup.index, Nat.card_eq_fintype_card] using Nat.card_le_card_of_surjective _ hs

lemma doubleRange_prod (B : Type v) [AddCommGroup B] :
    doubleRange (A×B)=(doubleRange A).prod (doubleRange B) := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact ⟨⟨y.1,rfl⟩,⟨y.2,rfl⟩⟩
  · rintro ⟨⟨a,ha⟩,⟨b,hb⟩⟩
    exact ⟨(a,b),Prod.ext ha hb⟩

lemma doubleRange_pi (ι : Type v) :
    doubleRange (ι → A)=AddSubgroup.pi Set.univ (fun _ => doubleRange A) := by
  classical
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    intro i _
    exact ⟨y i,rfl⟩
  · intro h
    have hh : ∀ i, ∃ y, (2:ℕ) • y=x i := fun i => h i (Set.mem_univ i)
    choose y hy using hh
    exact ⟨y,funext hy⟩

lemma doubleRange_int : doubleRange ℤ = AddSubgroup.zmultiples (2:ℤ) := by
  exact Int.range_nsmulAddMonoidHom 2

lemma free_index (n : ℕ) : (doubleRange (Fin n → ℤ)).index = 2^n := by
  rw [doubleRange_pi,AddSubgroup.index_pi]
  simp [doubleRange_int,Int.index_zmultiples]

lemma finite_index_eq_kernel [Finite A] : (doubleRange A).index = Nat.card (doubleKernel A) :=
  AddSubgroup.index_range

variable {A}

lemma doubleRange_map {B : Type v} [AddCommGroup B] (f : A ≃+ B) :
    (doubleRange A).map f.toAddMonoidHom=doubleRange B := by
  ext x
  constructor
  · rintro ⟨y,⟨z,hz⟩,rfl⟩
    refine ⟨f z,?_⟩
    change (2:ℕ) • f z=f y
    rw [←map_nsmul,f.injective.eq_iff]
    exact hz
  · rintro ⟨y,rfl⟩
    refine ⟨(2:ℕ) • f.symm y,⟨f.symm y,rfl⟩,?_⟩
    simp

lemma doubleRange_index_equiv {B : Type v} [AddCommGroup B] (f : A ≃+ B) :
    (doubleRange A).index=(doubleRange B).index := by
  rw [←doubleRange_map f]
  exact (AddSubgroup.index_map_equiv _ f).symm

lemma index_rank_formula {T : Type w} [AddCommGroup T] [Finite T] (n : ℕ)
    (f : A ≃+ (Fin n → ℤ)×T) :
    (doubleRange A).index = 2^n * Nat.card (doubleKernel A) := by
  rw [doubleRange_index_equiv f,doubleRange_prod,AddSubgroup.index_prod,free_index,
    finite_index_eq_kernel]
  congr 1
  exact (Nat.card_congr ((doubleKernel_equiv f).trans
    (doubleKernel_free_prod_equiv (Fin n) T))).symm

theorem exists_rank_le_one [AddGroup.FG A]
    (hindex : (doubleRange A).index ≤ 8) (hker : 4 ≤ Nat.card (doubleKernel A)) :
    ∃ (n : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      n ≤ 1 ∧ Nonempty (A ≃+ (Fin n → ℤ) × T) := by
  classical
  obtain ⟨n,ι,hi,p,hp,e,⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod A
  let T := DirectSum ι (fun i => ZMod (p i ^ e i))
  have hp0 : ∀ i, NeZero (p i ^ e i) := fun i => ⟨pow_ne_zero _ (hp i).ne_zero⟩
  let : Finite T := Finite.of_equiv (∀ i, ZMod (p i ^ e i)) DFinsupp.equivFunOnFintype.symm
  let g : A ≃+ (Fin n → ℤ)×T := f.trans
    ((Finsupp.linearEquivFunOnFinite ℤ ℤ (Fin n)).toAddEquiv.prodCongr (AddEquiv.refl T))
  have heq := index_rank_formula n g
  have hpow : 2^n ≤ 2 := by nlinarith
  have hn : n ≤ 1 := by
    by_contra h
    have hh : 2^2 ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega)
    norm_num at hh
    omega
  exact ⟨n,T,inferInstance,inferInstance,hn,⟨g⟩⟩

end SingleFold.AbstractRank

namespace SingleFold.CurveRank
open Descent WeierstrassCurve.Affine.Point

lemma double_torsion (P : E.Point) (hP : P=0 ∨ P=T0 ∨ P=T5 ∨ P=Tm5) :
    (2:ℕ) • P=0 := by
  rcases hP with rfl|rfl|rfl|rfl
  · simp
  all_goals
    rw [two_smul]
    simp only [T0,T5,Tm5]
    apply add_self_of_Y_eq
    norm_num [WeierstrassCurve.Affine.negY]

lemma four_le_doubleKernel : 4 ≤ Nat.card (AbstractRank.doubleKernel E.Point) := by
  let f : Fin 4 → AbstractRank.doubleKernel E.Point := fun i =>
    ⟨![0,T0,T5,Tm5] i,by
      apply double_torsion
      fin_cases i <;> simp⟩
  have hf : Function.Injective f := by
    intro i j h
    have hh := congrArg (fun x : AbstractRank.doubleKernel E.Point => x.val) h
    change ![0,T0,T5,Tm5] i = ![0,T0,T5,Tm5] j at hh
    fin_cases i <;> fin_cases j <;>
      simp_all [T0,T5,Tm5]
    all_goals norm_num at hh
  simpa using Nat.card_le_card_of_injective f hf

theorem rank_at_most_one :
    ∃ (n : ℕ) (T : Type) (_ : AddCommGroup T) (_ : Finite T),
      n ≤ 1 ∧ Nonempty (E.Point ≃+ (Fin n → ℤ) × T) := by
  apply AbstractRank.exists_rank_le_one
  · exact (AbstractRank.index_le_of_cover E.Point representatives representatives_cover).trans
      representatives_card
  · exact four_le_doubleKernel

end SingleFold.CurveRank

namespace SingleFold.ValuationRank
open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point

lemma equation {x y : ℚ} (h : E.Nonsingular x y) : y^2=x^3-25*x := by
  simpa [WeierstrassCurve.Affine.equation_iff,sub_eq_add_neg] using h.1

lemma val_add_eq {p : ℕ} [Fact p.Prime] {x y : ℚ}
    (hx : x ≠ 0) (hy : y ≠ 0) (hval : padicValRat p x ≠ padicValRat p y) :
    padicValRat p (x+y) = min (padicValRat p x) (padicValRat p y) := by
  apply padicValRat.add_eq_min _ hx hy hval
  intro h
  apply hval
  have he : x = -y := by linarith
  simp [he]

lemma val_25 : padicValRat 2 25=0 := by
  change padicValRat 2 (25:ℕ)=0
  rw [padicValRat.of_nat,padicValNat.eq_zero_of_not_dvd (by decide)]
  rfl
lemma val_4 : padicValRat 2 4=2 := by
  rw [show (4:ℚ)=2^2 by norm_num,padicValRat.pow]
  have hh : padicValRat 2 2=1 := padicValRat.self (by norm_num : 1 < (2:ℕ))
  simp [hh]

lemma val_sq_add {x : ℚ} (hx : padicValRat 2 x < 0) :
    padicValRat 2 (x^2+25)=2*padicValRat 2 x := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hh := val_add_eq (p:=2) (pow_ne_zero 2 hxn) (by norm_num : (25:ℚ) ≠ 0)
    (by rw [padicValRat.pow,val_25]; norm_num; omega)
  rw [padicValRat.pow,val_25,min_eq_left] at hh
  · simpa using hh
  · norm_num; omega

lemma val_sq_sub {x : ℚ} (hx : padicValRat 2 x < 0) :
    padicValRat 2 (x^2-25)=2*padicValRat 2 x := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hh := val_add_eq (p:=2) (pow_ne_zero 2 hxn) (by norm_num : (-25:ℚ) ≠ 0)
    (by rw [padicValRat.pow,padicValRat.neg,val_25]; norm_num; omega)
  rw [padicValRat.pow,padicValRat.neg,val_25,min_eq_left] at hh
  · simpa [sub_eq_add_neg] using hh
  · norm_num; omega

lemma duplication {x y : ℚ} (h : E.Nonsingular x y) (hy : y ≠ 0) :
    ∃ h' : E.Nonsingular ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)),
      (2:ℕ) • some x y h = some ((x^2+25)^2/(4*y^2)) (E.addY x x y (E.slope x x y y)) h' := by
  have hy' : y ≠ E.negY x y := by simpa [WeierstrassCurve.Affine.negY] using (show y ≠ -y by intro hh; apply hy; linarith)
  have hs : E.slope x x y y = (3*x^2-25)/(2*y) := by
    rw [slope_of_Y_ne rfl hy']
    simp
    congr 1 <;> ring
  have hx' : E.addX x x (E.slope x x y y) = (x^2+25)^2/(4*y^2) := by
    rw [WeierstrassCurve.Affine.addX,hs]
    dsimp
    field_simp
    have he := equation h
    linear_combination -32*x*he
  rw [two_smul,add_self_of_Y_ne hy']
  have he := E.nonsingular_add h h (by simpa using hy')
  rw [hx'] at he
  exact ⟨he,by simp only [hx']⟩

lemma double_val {x y : ℚ} (h : E.Nonsingular x y) (hx : padicValRat 2 x < 0) :
    ∃ (x' y' : ℚ) (h' : E.Nonsingular x' y'),
      (2:ℕ) • some x y h = some x' y' h' ∧
      padicValRat 2 x'=padicValRat 2 x-2 := by
  have hxn : x ≠ 0 := by intro he; simp [he] at hx
  have hs := val_sq_sub hx
  have hsn : x^2-25 ≠ 0 := by intro he; rw [he,padicValRat.zero] at hs; omega
  have he : y^2=x*(x^2-25) := by nlinarith only [equation h]
  have hyn : y ≠ 0 := by
    intro he'
    apply mul_ne_zero hxn hsn
    rw [←he,he']
    norm_num
  obtain ⟨h',hh⟩ := duplication h hyn
  refine ⟨_,_,h',hh,?_⟩
  have hp : x^2+25 ≠ 0 := by nlinarith [sq_nonneg x]
  rw [padicValRat.div (pow_ne_zero 2 hp) (mul_ne_zero (by norm_num) (pow_ne_zero 2 hyn)),
    padicValRat.pow,padicValRat.mul (by norm_num) (pow_ne_zero 2 hyn),val_4,
    he,padicValRat.mul hxn hsn,val_sq_add hx,hs]
  ring

lemma vx_double (P : E.Point) (h : vx P < 0) : vx ((2:ℕ) • P)=vx P-2 := by
  cases P with
  | zero => simp [vx] at h
  | some x y hp =>
    obtain ⟨x',y',h',hh,hv⟩ := double_val hp h
    rw [hh]
    exact hv

lemma vx_G : vx G = -2 := by
  change padicValRat 2 (25/4)= -2
  rw [padicValRat.div (by norm_num) (by norm_num),val_25,val_4]
  norm_num

lemma vx_dyadic (n : ℕ) : vx ((2^n:ℕ) • G)= -2-2*(n:ℤ) := by
  induction n with
  | zero => simpa using vx_G
  | succ n hn =>
    rw [pow_succ',mul_smul,vx_double _ (by rw [hn]; omega),hn]
    push_cast
    ring

lemma dyadic_injective : Function.Injective (fun n : ℕ => (2^n:ℕ) • G) := by
  intro n m h
  have hh := congrArg vx h
  rw [vx_dyadic,vx_dyadic] at hh
  omega

lemma G_nontorsion : ¬IsOfFinAddOrder G := by
  intro h
  have hf : (Set.range (fun n : ℕ => (2^n:ℕ) • G)).Finite :=
    h.finite_multiples.subset (by rintro _ ⟨n,rfl⟩; exact ⟨2^n,rfl⟩)
  exact (Set.infinite_range_of_injective dyadic_injective) hf

end SingleFold.ValuationRank

namespace SingleFold.CurveRank
open Descent

theorem rank_one : ∃ (T : Type) (_ : AddCommGroup T) (_ : Finite T),
    Nonempty (E.Point ≃+ (Fin 1 → ℤ) × T) := by
  obtain ⟨n,T,hT,hfin,hn,⟨f⟩⟩ := rank_at_most_one
  rcases (show n=0 ∨ n=1 by omega) with rfl|rfl
  · let : Finite E.Point := Finite.of_equiv ((Fin 0 → ℤ)×T) f.symm.toEquiv
    exact False.elim (ValuationRank.G_nontorsion (isOfFinAddOrder_of_finite _))
  · exact ⟨T,hT,hfin,⟨f⟩⟩

end SingleFold.CurveRank

end OAI

-- ---- from OAI.NumberTheory.SingleFold.HeightGrowth ----
namespace OAI

namespace SingleFold.GrowthEstimate
open Filter
open scoped Topology

variable {W : ℕ → ℕ} {a c : ℝ}

lemma sequence_unbounded (hW : ∀ j, 0<W j) (ha : 0<a)
    (happrox : ∀ j, 1≤j → |Real.log (W j:ℝ)-a*(j:ℝ)^2|≤c) (U : ℕ) : ∃ j, U<W j := by
  obtain ⟨n,hn⟩ := exists_nat_gt (max ((U+c+1)/a+1) 1)
  have hn1 : 1<n := by exact_mod_cast lt_of_le_of_lt (le_max_right _ _) hn
  have hn' : (U+c+1)/a+1 < (n:ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hh := (abs_le.mp (happrox n (by omega))).1
  have hlog := Real.log_le_sub_one_of_pos (by exact_mod_cast hW n : (0:ℝ)<W n)
  have hn2 : (1:ℝ)<n := by exact_mod_cast hn1
  have hdiv : (U:ℝ)+c+1 < (n-1:ℝ)*a := (div_lt_iff₀ ha).mp (show ((U:ℝ)+c+1)/a < (n:ℝ)-1 by linarith)
  have hn3 : (n-1:ℝ)*a < a*(n:ℝ)^2 := by nlinarith [mul_lt_mul_of_pos_left (show (n:ℝ)-1 < (n:ℝ)^2 by nlinarith) ha]
  have hu : (U:ℝ)<W n := by linarith
  exact ⟨n,by exact_mod_cast hu⟩

end SingleFold.GrowthEstimate

namespace SingleFold.HeightWindow

end SingleFold.HeightWindow

end OAI

-- ---- from OAI.NumberTheory.SingleFold.EllipticGrowth ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.EllipticModel
open WeierstrassCurve.Affine.Point
lemma Hx_pos (Q : E.Point) : 0<Hx Q := by
  cases Q with
  | zero => exact Nat.zero_lt_one
  | some x y h => exact lt_of_lt_of_le x.den_pos (le_max_right _ _)
lemma log_Hx (Q : E.Point) : Real.log (Hx Q:ℝ)=CurveHeight.naiveHeight Q := by
  cases Q with
  | zero => simp only [Hx,Nat.cast_one,Real.log_one,←zero_def,CurveHeight.naiveHeight_zero]
  | some x y h => exact (CurveHeight.naiveHeight_some h).symm
lemma Hx_neg (Q : E.Point) : Hx (-Q)=Hx Q := by
  cases Q with
  | zero => rfl
  | some x y h => rfl

variable {T : Type} [AddCommGroup T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
lemma point_add (n m : ℤ) (t s : T) : point f (n+m) (t+s)=point f n t+point f m s := by
  apply f.injective
  simp [point]
  rfl
lemma P_nontorsion : ¬IsOfFinAddOrder (P f) := by
  intro h
  obtain ⟨n,hn,hne⟩ := h.exists_nsmul_eq_zero
  have hh := congrArg (fun Q => (f Q).1 0) hne
  simp [P,point] at hh
  omega
lemma W_pos (m : ℕ) (Q : E.Point) : 0<W m Q := Hx_pos _
lemma sequence_zero (m : ℕ) : sequence f m 0=1 := by
  unfold sequence W
  rw [zero_nsmul,nsmul_zero]
  rfl
lemma W_neg (m : ℕ) (Q : E.Point) : W m (-Q)=W m Q := by
  change Hx (m • (-Q))=Hx (m • Q)
  rw [show m • (-Q)= -(m • Q) from (nsmulAddMonoidHom (α:=E.Point) m).map_neg Q,Hx_neg]
lemma sequence_approx (m : ℕ) (c : ℝ)
    (hc : ∀ Q : E.Point, |CurveHeight.naiveHeight Q-2*CurveHeight.canonicalHeight Q|≤c) (j : ℕ) :
    |Real.log (sequence f m j:ℝ)-(2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f))*(j:ℝ)^2|≤c := by
  have hh := hc (m • (j • P f))
  rw [CurveHeight.canonicalHeight_nsmul,CurveHeight.canonicalHeight_nsmul] at hh
  rw [sequence,W,log_Hx]
  convert hh using 1
  congr 1
  ring
lemma xcoord_neg (Q : E.Point) : xcoord (-Q)=xcoord Q := by cases Q <;> rfl
lemma ycoord_neg (Q : E.Point) : ycoord (-Q)= -ycoord Q := by
  cases Q with
  | zero => rfl
  | some x y h => change E.negY x y= -y; simp [WeierstrassCurve.Affine.negY]
lemma xy_unique {Q R : E.Point} (hQ : Q≠0) (hR : R≠0)
    (hx : xcoord Q=xcoord R) (hyQ : 0≤ycoord Q) (hyR : 0≤ycoord R) : Q=R := by
  cases Q with
  | zero => exact False.elim (hQ rfl)
  | some x y h =>
    cases R with
    | zero => exact False.elim (hR rfl)
    | some z w h' =>
      change x=z at hx
      subst z
      have he := CurveHeight.E_equation h
      have he' := CurveHeight.E_equation h'
      have hy : y=w := by
        change 0≤y at hyQ
        change 0≤w at hyR
        nlinarith
      subst w
      rfl
lemma index_point (n : ℤ) (t : T) : index f (point f n t)=n := by simp [index,point]
lemma index_zero : index f 0=0 := by simp [index]
lemma index_add (Q R : E.Point) : index f (Q+R)=index f Q+index f R := by simp [index]
lemma index_neg (Q : E.Point) : index f (-Q)= -index f Q := by simp [index]
lemma point_ne_zero {n : ℤ} (hn : n≠0) (t : T) : point f n t≠0 := by
  intro h
  have hh := congrArg (index f) h
  rw [index_point,index_zero] at hh
  exact hn hh

lemma representative_max {m : ℕ} {Q R : E.Point} (hQ : Representative f m Q)
    (hidx : (index f R).natAbs=(index f Q).natAbs) : xcoord R≤xcoord Q := by
  have hidx' : index f R=index f Q ∨ index f R= -index f Q := by
    exact Int.natAbs_eq_natAbs_iff.mp hidx
  rcases hidx' with h|h
  · let t := (f R).2-(f Q).2
    have he : R=Q+point f 0 t := by
      apply f.injective
      simp only [map_add,point,AddEquiv.apply_symm_apply]
      apply Prod.ext
      · funext i
        change (f R).1 i=(f Q).1 i+0
        simpa only [add_zero,index,show i=(0:Fin 1) from Subsingleton.elim _ _] using h
      · simp [t]
    rw [he]
    exact (hQ.2.2.2 t).2
  · let t := -(f R).2-(f Q).2
    have he : -R=Q+point f 0 t := by
      apply f.injective
      simp only [map_add,map_neg,point,AddEquiv.apply_symm_apply]
      apply Prod.ext
      · funext i
        change -(f R).1 i=(f Q).1 i+0
        have hi : i=(0:Fin 1) := Subsingleton.elim _ _
        simp only [hi,add_zero]
        change -(index f R)=index f Q
        rw [h,neg_neg]
      · simp [t]
    rw [←xcoord_neg R,he]
    exact (hQ.2.2.2 t).2
lemma representative_unique {m : ℕ} {Q R : E.Point}
    (hQ : Representative f m Q) (hR : Representative f m R)
    (hidx : (index f Q).natAbs=(index f R).natAbs) : Q=R :=
  xy_unique hQ.1 hR.1 (le_antisymm (representative_max f hR hidx) (representative_max f hQ hidx.symm)) hQ.2.1 hR.2.1

lemma representative_exists [Finite T] (m : ℕ) (hm : Even m)
    (hstrict : StrictMono (sequence f m)) (j : ℕ) (hj : 1≤j) :
    ∃! Q : E.Point, Representative f m Q ∧ (index f Q).natAbs=j := by
  obtain ⟨t,ht⟩ := Finite.exists_max (fun t : T => xcoord (point f j t))
  let A := point f j t
  have hj0 : (j:ℤ)≠0 := by omega
  have hA : A≠0 := point_ne_zero f hj0 t
  have hiA : (index f A).natAbs=j := by simp [A,index_point]
  have hWA : 1<W m A := by
    rw [W_index f m hm,hiA,←sequence_zero f m]
    exact hstrict (by omega)
  have htA (s : T) : A+point f 0 s≠0 ∧ xcoord (A+point f 0 s)≤xcoord A := by
    change point f j t+point f 0 s≠0 ∧ _
    rw [←point_add,add_zero]
    exact ⟨point_ne_zero f hj0 _,ht _⟩
  have hex : ∃ Q, Representative f m Q ∧ (index f Q).natAbs=j := by
    by_cases hy : 0≤ycoord A
    · exact ⟨A,⟨hA,hy,hWA,htA⟩,hiA⟩
    · refine ⟨-A,⟨neg_ne_zero.mpr hA,?_,?_,?_⟩,?_⟩
      · rw [ycoord_neg]; linarith
      · rw [W_neg]; exact hWA
      · intro s
        have he : -A+point f 0 s= -(A+point f 0 (-s)) := by
          have hn : point f 0 (-s)= -point f 0 s := by
            apply f.injective; simp [point]; rfl
          rw [hn]; abel
        rw [he,xcoord_neg,xcoord_neg]
        exact ⟨neg_ne_zero.mpr (htA (-s)).1,(htA (-s)).2⟩
      · rw [index_neg,Int.natAbs_neg,hiA]
  obtain ⟨Q,hQ⟩ := hex
  refine ⟨Q,hQ,?_⟩
  intro R hR
  exact representative_unique f hR.1 hQ.1 (hR.2.trans hQ.2.symm)

theorem height_constants : ∃ (c : ℝ) (κ m : ℕ),
    0 < c ∧ 0 < κ ∧ 0 < m ∧ Even m ∧
    (∀ Q : E.Point, |CurveHeight.naiveHeight Q-2*CurveHeight.canonicalHeight Q|≤c) ∧
    2*c < 2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f) ∧
    6*c < Real.log κ ∧ Real.log κ < 2*(2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f))-6*c := by
  obtain ⟨c,hc,herr⟩ := CurveHeight.uniform_height
  have hp := CurveHeight.canonicalHeight_pos (P_nontorsion f)
  obtain ⟨κ,hκ⟩ := exists_nat_gt (Real.exp (6*c))
  have hκpos : 0<κ := by exact_mod_cast lt_trans (Real.exp_pos _) hκ
  have hlog : 6*c<Real.log κ := by
    rw [←Real.log_exp (6*c)]
    exact Real.log_lt_log (Real.exp_pos _) hκ
  let B := max (2*c) ((Real.log κ+6*c)/2)
  obtain ⟨d,hd⟩ := exists_nat_gt (max (B/CurveHeight.canonicalHeight (P f)+1) 1)
  have hd1 : (1:ℝ)<d := lt_of_le_of_lt (le_max_right _ _) hd
  have hdn1 : 1<d := by exact_mod_cast hd1
  have hdB : B/CurveHeight.canonicalHeight (P f)+1<(d:ℝ) := lt_of_le_of_lt (le_max_left _ _) hd
  have hB : B<(d:ℝ)*CurveHeight.canonicalHeight (P f) := by
    apply (div_lt_iff₀ hp).mp
    linarith
  have hBd : B<8*(d:ℝ)^2*CurveHeight.canonicalHeight (P f) := by
    have hmul := mul_lt_mul_of_pos_right (show (d:ℝ)<8*(d:ℝ)^2 by nlinarith) hp
    exact hB.trans hmul
  refine ⟨c,κ,2*d,hc,hκpos,by omega,even_two_mul d,herr,?_,hlog,?_⟩
  · have hb := le_max_left (2*c) ((Real.log κ+6*c)/2)
    dsimp [B] at hBd
    push_cast
    nlinarith
  · have hb := le_max_right (2*c) ((Real.log κ+6*c)/2)
    dsimp [B] at hBd
    push_cast
    nlinarith
lemma neighbor_index (n : ℤ) : max (n+1).natAbs (n-1).natAbs=n.natAbs+1 := by
  apply Int.natCast_inj.mp
  simp only [Nat.cast_max,Int.natCast_natAbs,Nat.cast_add,Nat.cast_one]
  rcases le_total 0 n with hn|hn
  · rw [abs_of_nonneg hn,abs_of_nonneg (by omega : 0≤n+1),max_eq_left (by
      rw [abs_le]; omega)]
  · rw [abs_of_nonpos hn,abs_of_nonpos (by omega : n-1≤0),max_eq_right (by
      rw [abs_le]; omega)]
    ring
lemma index_P : index f (P f)=1 := by rw [P,index_point]
lemma neighbor_max [Finite T] (m : ℕ) (hm : Even m) (hs : StrictMono (sequence f m)) (Q : E.Point) :
    max (W m (Q+P f)) (W m (Q-P f))=sequence f m ((index f Q).natAbs+1) := by
  rw [W_index f m hm,W_index f m hm,←hs.monotone.map_max]
  have hi : index f (Q-P f)=index f Q-1 := by
    change (f (Q-P f)).1 0= _
    simp only [map_sub,Prod.fst_sub,Pi.sub_apply]
    change index f Q-index f (P f)= _
    rw [index_P]
  rw [hi,index_add,index_P,neighbor_index]
lemma double_index (Q : E.Point) : (index f ((2:ℕ) • Q)).natAbs=2*(index f Q).natAbs := by
  rw [two_nsmul,index_add,←two_mul,Int.natAbs_mul]
  rfl

lemma representative_index_pos [Finite T] {m : ℕ} (hm : Even m) {Q : E.Point}
    (hQ : Representative f m Q) : 1 ≤ (index f Q).natAbs := by
  have hw := hQ.2.2.1
  rw [W_index f m hm] at hw
  by_contra hn
  have hi : (index f Q).natAbs=0 := by omega
  rw [hi,sequence_zero] at hw
  omega

lemma sequence_one (m : ℕ) : sequence f m 1=W m (P f) := by simp only [sequence,one_nsmul]
lemma bracket_iff [Finite T] {m : ℕ} (hm : Even m) (hs : StrictMono (sequence f m))
    (u : ℕ) (Q : E.Point) : Bracket f m u Q ↔
      sequence f m (index f Q).natAbs ≤ u+sequence f m 1 ∧
        u+sequence f m 1 < sequence f m ((index f Q).natAbs+1) := by
  dsimp only [Bracket]
  rw [W_index f m hm Q,←sequence_one,neighbor_max f m hm hs]
lemma window_iff [Finite T] {m κ : ℕ} {a c : ℝ} (hm : Even m) (hs : StrictMono (sequence f m))
    (hc : 0 ≤ c) (hκ : 0 < κ) (h₁ : 6*c < Real.log κ) (h₂ : Real.log κ < 2*a-6*c)
    (ha : ∀ j, 1 ≤ j → |Real.log (sequence f m j:ℝ)-a*(j:ℝ)^2| ≤ c)
    {Q R : E.Point} (hQ : Representative f m Q) (hR : Representative f m R) :
    Window f m κ Q R ↔ (index f R).natAbs=(index f Q).natAbs^2 := by
  dsimp only [Window]
  rw [W_index f m hm (2 • Q),W_index f m hm R,W_index f m hm Q,
    ←sequence_one,neighbor_max f m hm hs,double_index]
  exact HeightWindow.square_window (fun j => W_pos _ _) ha hc hκ h₁ h₂
    (representative_index_pos f hm hQ) (representative_index_pos f hm hR)

lemma growth_pair_existsUnique [Finite T] {m κ : ℕ} {a c : ℝ}
    (hm : Even m) (hs : StrictMono (sequence f m))
    (hu : ∀ U, ∃ j, U < sequence f m j) (hc : 0 ≤ c) (hκ : 0 < κ)
    (h₁ : 6*c < Real.log κ) (h₂ : Real.log κ < 2*a-6*c)
    (ha : ∀ j, 1 ≤ j → |Real.log (sequence f m j:ℝ)-a*(j:ℝ)^2| ≤ c) (u : ℕ) :
    ∃! A, GrowthPair f m κ u A := by
  obtain ⟨k,hk,hku⟩ := GrowthEstimate.bracket_unique hs hu u
  obtain ⟨Q,⟨hQ,hiQ⟩,_⟩ := representative_exists f m hm hs k hk.1
  obtain ⟨R,⟨hR,hiR⟩,_⟩ := representative_exists f m hm hs (k^2) (by nlinarith [hk.1])
  have hbQ : Bracket f m u Q := (bracket_iff f hm hs u Q).mpr (by simpa only [hiQ] using hk.2)
  have hwQR : Window f m κ Q R := (window_iff f hm hs hc hκ h₁ h₂ ha hQ hR).mpr (by rw [hiQ,hiR])
  refine ⟨(Q,R),⟨hQ,hbQ,hR,hwQR⟩,?_⟩
  rintro ⟨Q',R'⟩ ⟨hQ',hbQ',hR',hwQR'⟩
  have hiQ' : (index f Q').natAbs=k := hku _ ⟨representative_index_pos f hm hQ',
    (bracket_iff f hm hs u Q').mp hbQ'⟩
  have hQQ : Q'=Q := representative_unique f hQ' hQ (hiQ'.trans hiQ.symm)
  have hiR' := (window_iff f hm hs hc hκ h₁ h₂ ha hQ' hR').mp hwQR'
  have hRR : R'=R := representative_unique f hR' hR (by rw [hiR',hiQ',hiR])
  exact Prod.ext hQQ hRR

theorem growth_model [Finite T] : ∃ (m κ : ℕ) (g : ℕ → ℕ) (δ : ℝ) (u₀ : ℕ),
    0 < m ∧ Even m ∧ 0 < κ ∧ 0 < δ ∧ 4 ≤ u₀ ∧
    (∀ u, ∃! A : E.Point × E.Point, GrowthPair f m κ u A) ∧
    (∀ u v, (∃ A, GrowthPair f m κ u A ∧ W m A.2=v) ↔ v=g u) ∧
    (∀ u, u₀ ≤ u → δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧
      Real.log (g u:ℝ) < (u:ℝ)*Real.log (u:ℝ)) := by
  classical
  obtain ⟨c,κ,m,hc,hκ,hm,heven,herr,hlarge,hlog,hlog'⟩ := height_constants f
  let a : ℝ := 2*(m:ℝ)^2*CurveHeight.canonicalHeight (P f)
  have hp := CurveHeight.canonicalHeight_pos (P_nontorsion f)
  have ha : 0 < a := by dsimp [a]; positivity
  have happ : ∀ j, 1 ≤ j → |Real.log (sequence f m j:ℝ)-a*(j:ℝ)^2| ≤ c :=
    fun j _ => sequence_approx f m c herr j
  have hs : StrictMono (sequence f m) := GrowthEstimate.sequence_strict
    (fun j => W_pos _ _) (sequence_zero f m) hc.le hlarge happ
  have hunb := GrowthEstimate.sequence_unbounded (fun j => W_pos m (j • P f)) ha happ
  have hpair (u) := growth_pair_existsUnique f heven hs hunb hc.le hκ hlog hlog' happ u
  let A (u : ℕ) : E.Point × E.Point := Classical.choose (hpair u)
  have hA (u) : GrowthPair f m κ u (A u) := (Classical.choose_spec (hpair u)).1
  let g (u) := W m (A u).2
  obtain ⟨u₀,hu₀,hu⟩ := GrowthEstimate.eventual_output (fun j => W_pos m (j • P f)) ha hc.le happ
  refine ⟨m,κ,g,1/(128*a),u₀,hm,heven,hκ,by positivity,hu₀,hpair,?_,?_⟩
  · intro u v
    constructor
    · rintro ⟨B,hB,hv⟩
      have hBA : B=A u := (Classical.choose_spec (hpair u)).2 B hB
      subst B
      exact hv.symm
    · rintro rfl; exact ⟨A u,hA u,rfl⟩
  · intro u huu
    have hQ := (hA u).1
    have hR := (hA u).2.2.1
    have hb := (bracket_iff f heven hs u (A u).1).mp (hA u).2.1
    have hi := (window_iff f heven hs hc.le hκ hlog hlog' happ hQ hR).mp (hA u).2.2.2
    have hg : g u=sequence f m ((index f (A u).1).natAbs^2) := by
      dsimp [g]; rw [W_index f m heven,hi]
    rw [hg]
    exact hu u huu _ (representative_index_pos f heven hQ) hb

end SingleFold.EllipticModel

namespace SingleFold.GrowthCompilation
open Compiler PointCompiler
section
variable {T α : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
variable {Q R : (α → ℕ) → E.Point}
end

section
variable {T : Type} [AddCommGroup T] [Finite T]
variable (f : E.Point ≃+ (Fin 1 → ℤ)×T)
end

theorem growth : ∃ (g : ℕ → ℕ) (δ : ℝ) (u₀ : ℕ), 0 < δ ∧ 4 ≤ u₀ ∧
    SF (fun z : Fin 2 → ℕ => z 1=g (z 0)) ∧
    (∀ u, u₀ ≤ u → δ*(Real.log (u:ℝ))^2 < Real.log (g u:ℝ) ∧
      Real.log (g u:ℝ) < (u:ℝ)*Real.log (u:ℝ)) := by
  obtain ⟨T,hT,hfin,⟨f⟩⟩ := CurveRank.rank_one
  let := hT
  let := hfin
  obtain ⟨m,κ,g,δ,u₀,_,_,_,hδ,hu₀,hunique,hgraph,hest⟩ := EllipticModel.growth_model f
  exact ⟨g,δ,u₀,hδ,hu₀,(graph_sf f m κ hunique).congr (fun z => hgraph (z 0) (z 1)),hest⟩
end SingleFold.GrowthCompilation

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Power ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = t hc := @dif_pos c h hc α t e

namespace OAI

namespace SingleFold.PowerEstimate
lemma choose_ell {δ : ℝ} (hδ : 0 < δ) : ∃ ell : ℕ, 1 ≤ ell ∧ 3 < δ*(ell:ℝ)*Real.log 2 := by
  have hlog : 0 < Real.log (2:ℝ) := Real.log_pos (by norm_num)
  obtain ⟨ell,hell⟩ := exists_nat_gt (3/(δ*Real.log 2))
  refine ⟨ell,?_,?_⟩
  · have : (0:ℝ) < ell := lt_trans (div_pos (by norm_num) (mul_pos hδ hlog)) hell
    have hp : 0<ell := by exact_mod_cast this
    omega
  · have hh := (div_lt_iff₀ (mul_pos hδ hlog)).mp hell
    nlinarith

end SingleFold.PowerEstimate

namespace SingleFold.PowerSystem
open PowerEstimate

variable {g : ℕ → ℕ} {δ : ℝ} {ell u₀ : ℕ}
variable (hδ : 0<δ) (hell : 1≤ell) (h₀ : 4≤u₀)
variable (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ))
include hδ hell h₀ hg
lemma sound {b n c : ℕ} {w : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) : 2≤b ∧ c=b^n := by
  have hp := pinned hδ hell h₀ hg hw
  have hbds := input_bounds (c:=c) (n:=n) (b:=b) hell h₀
  rcases hw with ⟨hb,hu,hv,hX,hY,hF,hFv,hH,hHv,hq,hq',hdiv,hr⟩
  rw [←hu] at hbds
  rw [hp.2.1,hp.2.2.2] at hdiv
  rw [hp.2.2.2] at hr
  have hua : 1<w 0 := by omega
  have hba : 1<b*w 0 := by nlinarith
  simp only [py,dite_eq_left hua,dite_eq_left hba] at hdiv hr
  exact ⟨hb,PellSystem.quotient_sound hb hbds.2.1 hdiv hr⟩
lemma unique {b n c : ℕ} {w w' : Fin 9 → ℕ} (hw : System g ell u₀ b n c w) (hw' : System g ell u₀ b n c w') : w=w' := by
  have hp := pinned hδ hell h₀ hg hw
  have hp' := pinned hδ hell h₀ hg hw'
  rcases hw with ⟨hb,hu,hv,hX,hY,hF,hFv,hH,hHv,hq,hq',hdiv,hr⟩
  rcases hw' with ⟨_,hu',hv',hX',hY',hF',hFv',hH',hHv',hqq,hqq',hdiv',hr'⟩
  have h0 : w 0=w' 0 := hu.trans hu'.symm
  have h1 : w 1=w' 1 := by rw [hv,hv',h0]
  have h2 : w 2=w' 2 := by rw [hp.1,hp'.1,h0]
  have h3 : w 3=w' 3 := by rw [hp.2.1,hp'.2.1,h0]
  have h4 : w 4=w' 4 := by rw [hp.2.2.1,hp'.2.2.1,h0]
  have h5 : w 5=w' 5 := by rw [hp.2.2.2,hp'.2.2.2,h0]
  have hu4 : 4≤w' 0 := by rw [hu']; exact h₀.trans (input_bounds (c:=c) (n:=n) (b:=b) hell h₀).1
  have h6 : w 6=w' 6 := by
    rw [h0,h3] at hq
    have hh : 2≤b*w' 0 := by nlinarith only [hb,hu4]
    apply Nat.eq_of_mul_eq_mul_left (show 0<b*w' 0-1 by omega)
    omega
  have h7 : w 7=w' 7 := by
    rw [h0,h5] at hq'
    apply Nat.eq_of_mul_eq_mul_left (show 0<w' 0-1 by omega)
    omega
  have h8 : w 8=w' 8 := by rw [h3,h5] at hdiv; omega
  funext j; fin_cases j <;> assumption
end SingleFold.PowerSystem

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g : (α → ℕ) → ℕ}
end SingleFold.Compiler.ScalarSF

namespace SingleFold.PowerCompilation
open Compiler
lemma system_sf (g : ℕ → ℕ) (ell u₀ : ℕ)
    (hg : SF (fun z : Fin 2 → ℕ => z 1=g (z 0))) :
    SF (fun z : Fin 3⊕Fin 9 → ℕ => PowerSystem.System g ell u₀ (z (.inl 0)) (z (.inl 1)) (z (.inl 2)) (z ∘ Sum.inr)) := by
  let α := Fin 3⊕Fin 9
  let a (i : α) : ScalarSF (fun z : α → ℕ => z i) := ScalarSF.proj i
  let b := a (.inl 0)
  let n := a (.inl 1)
  let c := a (.inl 2)
  let u := a (.inr 0)
  let v := a (.inr 1)
  let X := a (.inr 2)
  let F := a (.inr 3)
  let Y := a (.inr 4)
  let H := a (.inr 5)
  let q := a (.inr 6)
  let q' := a (.inr 7)
  let r := a (.inr 8)
  let k (j : ℕ) : ScalarSF (fun _ : α → ℕ => j) := ScalarSF.const j
  have hinput := u.eq (((((c.add (k 1)).pow ell).mul (n.add (k 1))).mul (b.add (k 1))).add (k u₀))
  have hgraph : SF (fun z : α → ℕ => z (.inr 1)=g (z (.inr 0))) :=
    by
      simpa using hg.reindex (fun j => if j=0 then (Sum.inr 0 : α) else Sum.inr 1)
  have heq1 := ((X.pow 2).add (F.pow 2)).eq ((k 1).add (((b.mul u).pow 2).mul (F.pow 2)))
  have heq2 := ((Y.pow 2).add (H.pow 2)).eq ((k 1).add ((u.pow 2).mul (H.pow 2)))
  have hres1 := F.eq ((n.add (k 1)).add (((b.mul u).sub (k 1)).mul q))
  have hres2 := H.eq ((n.add (k 1)).add ((u.sub (k 1)).mul q'))
  exact ((k 2).le b).and (hinput.and (hgraph.and (heq1.and (heq2.and
    (((k 0).lt F).and ((F.lt v).and (((k 0).lt H).and ((H.lt v).and
      (hres1.and (hres2.and ((F.eq ((c.mul H).add r)).and (r.lt H))))))))))))

lemma power_of_growth (g : ℕ → ℕ) (δ : ℝ) (u₀ : ℕ) (hδ : 0<δ) (h₀ : 4≤u₀)
    (hgraph : SF (fun z : Fin 2 → ℕ => z 1=g (z 0)))
    (hg : ∀ u, u₀≤u → δ*(Real.log (u:ℝ))^2<Real.log (g u:ℝ) ∧ Real.log (g u:ℝ)<(u:ℝ)*Real.log (u:ℝ)) :
    SF (fun z : Fin 3 → ℕ => 2≤z 0 ∧ z 2=z 0^z 1) := by
  obtain ⟨ell,hell,hell'⟩ := PowerEstimate.choose_ell hδ
  have h := (system_sf g ell u₀ hgraph).ex (by
    intro z w w' hw hw'
    exact PowerSystem.unique hδ hell h₀ hg hw hw')
  refine h.congr ?_
  intro z
  constructor
  · rintro ⟨w,hw⟩
    exact PowerSystem.sound hδ hell h₀ hg hw
  · rintro ⟨hb,hc⟩
    obtain ⟨w,hw⟩ := PowerSystem.complete hδ hell h₀ hg hell' (n:=z 1) hb
    refine ⟨w, ?_⟩
    change PowerSystem.System g ell u₀ (z 0) (z 1) (z 2) w
    rw [hc]
    exact hw

theorem power : SF (fun z : Fin 3 → ℕ => 2≤z 0 ∧ z 2=z 0^z 1) := by
  obtain ⟨g,δ,u₀,hδ,h₀,hgraph,hg⟩ := GrowthCompilation.growth
  exact power_of_growth g δ u₀ hδ h₀ hgraph hg
end SingleFold.PowerCompilation

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Binary ----
namespace OAI

namespace SingleFold.Binary

lemma le {x y : ℕ} (h : Bits x y) : x≤y := by
  have hh := (choose_odd_iff x y).mpr h
  by_contra hl
  rw [Nat.choose_eq_zero_of_lt (by omega)] at hh
  omega

lemma sound {x y : ℕ} {w : Fin 7 → ℕ} (hw : System x y w) : Bits x y := by
  rcases hw with ⟨hxy,hB,hH,hN,he,hd,hr,ht⟩
  have hh := (extract_unique he hd hr).2.1
  have hpow : 2^y<2^(y+1) := by simp [pow_succ]
  rw [hN,hH,hB,choose_digit hxy hpow] at hh
  apply (choose_odd_iff x y).mp
  rw [← hh,ht]
  omega

lemma unique {x y : ℕ} {w v : Fin 7 → ℕ} (hw : System x y w) (hv : System x y v) : w=v := by
  rcases hw with ⟨_,hB,hH,hN,he,hd,hr,ht⟩
  rcases hv with ⟨_,hB',hH',hN',he',hd',hr',ht'⟩
  have h0 : w 0=v 0 := hB.trans hB'.symm
  have h1 : w 1=v 1 := by rw [hH,hH',h0]
  have h2 : w 2=v 2 := by rw [hN,hN',h0]
  have hh := extract_unique he hd hr
  have hh' := extract_unique he' hd' hr'
  rw [h0,h1,h2] at hh
  have h3 := hh.2.2.trans hh'.2.2.symm
  have h4 := hh.2.1.trans hh'.2.1.symm
  have h5 := hh.1.trans hh'.1.symm
  have h6 : w 6=v 6 := by omega
  funext i; fin_cases i <;> assumption

lemma complete {x y : ℕ} (h : Bits x y) : ∃ w, System x y w := by
  let B:=2^(y+1)
  let H:=B^x
  let N:=(B+1)^y
  let d:=N/H%B
  have hB : 0<B := by positivity
  have hH : 0<H := by positivity
  have hpow : 2^y<B := by dsimp [B]; simp [pow_succ]
  have hd : d=y.choose x := choose_digit (le h) hpow
  have ho : d%2=1 := by rw [hd]; exact (choose_odd_iff x y).mpr h
  refine ⟨![B,H,N,N/H/B,d,N%H,d/2],le h,rfl,rfl,rfl,?_,Nat.mod_lt _ hB,Nat.mod_lt _ hH,?_⟩
  · change N=N/H/B*B*H+(N/H%B)*H+N%H
    have hq := Nat.mod_add_div (N/H) B
    have hn := Nat.mod_add_div N H
    nlinarith only [hq,hn]
  · change d=2*(d/2)+1
    omega
end SingleFold.Binary

namespace SingleFold.Compiler.MapSF
lemma vector {α ι : Type} [Finite ι] {f : ι → (α → ℕ) → ℕ}
    (h : ∀ i, ScalarSF (f i)) : MapSF (fun z i => f i z) := by
  exact ((MapSF.proj (fun i => (i,()))).comp (MapSF.all h)).congr (by intros; rfl)
end SingleFold.Compiler.MapSF

namespace SingleFold.Compiler.ScalarSF
variable {α : Type} {f g h : (α → ℕ) → ℕ}
lemma powerRel (hf : ScalarSF f) (hg : ScalarSF g) (hh : ScalarSF h) :
    SF (fun z => 2≤f z ∧ h z=f z^g z) := by
  have hv : MapSF (fun z => ![f z,g z,h z]) := MapSF.vector (by intro i; fin_cases i <;> assumption)
  exact hv.pullback PowerCompilation.power
end SingleFold.Compiler.ScalarSF

namespace SingleFold.Binary
open Compiler
lemma system_sf : SF (fun z : Fin 2⊕Fin 7 → ℕ => System (z (.inl 0)) (z (.inl 1)) (z ∘ Sum.inr)) := by
  let α:=Fin 2⊕Fin 7
  let a (i : α) : ScalarSF (fun z : α → ℕ => z i) := ScalarSF.proj i
  let x:=a (.inl 0); let y:=a (.inl 1)
  let B:=a (.inr 0); let H:=a (.inr 1); let N:=a (.inr 2)
  let s:=a (.inr 3); let d:=a (.inr 4); let r:=a (.inr 5); let t:=a (.inr 6)
  let k (j : ℕ) : ScalarSF (fun _ : α → ℕ => j) := ScalarSF.const j
  have h := (x.le y).and (((k 2).powerRel (y.add (k 1)) B).and
    ((B.powerRel x H).and (((B.add (k 1)).powerRel y N).and
      ((N.eq ((((s.mul B).mul H).add (d.mul H)).add r)).and
        ((d.lt B).and ((r.lt H).and (d.eq (((k 2).mul t).add (k 1)))))))))
  refine h.congr ?_
  intro z

  constructor
  · rintro ⟨hxy,⟨_,hB⟩,⟨_,hH⟩,⟨_,hN⟩,he⟩
    exact ⟨hxy,hB,hH,hN,he⟩
  · rintro ⟨hxy,hB,hH,hN,he⟩
    have hb : 2≤z (.inr 0) := by
      change 2≤(z ∘ Sum.inr) 0
      rw [hB,pow_succ]
      have := Nat.two_pow_pos (z (.inl 1))
      omega
    exact ⟨hxy,⟨by omega,hB⟩,⟨hb,hH⟩,⟨by omega,hN⟩,he⟩

theorem bits : SF (fun z : Fin 2 → ℕ => Bits (z 0) (z 1)) := by
  have h := system_sf.ex (by intro z w w' hw hw'; exact unique hw hw')
  refine h.congr ?_
  intro z
  exact ⟨fun ⟨w,hw⟩ => sound hw,complete⟩
end SingleFold.Binary

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter

section
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable [Fintype Q] [Fintype J]
end

open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable {M : Machine Q J} {d : J → ℕ} {v : Witness Q J}
namespace System

section
variable (h : System M d v)
include h
omit [DecidableEq Q] [DecidableEq J] h in
lemma Cpos : 0 < baseC Q d := by simp [baseC]
lemma Bpos : 0 < v.B := by have := h.bound; have := (System.Cpos (Q:=Q) (d:=d)); omega
lemma Bfour : 4 ≤ v.B := by have := h.base; have := h.Bpos; omega
end

section
variable (h : System M d v)
include h
end

variable (h : System M d v)
include h
end System
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterBounds ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Packed
lemma exists_scale {L : ℕ} (hL : 0 < L) : ∃ w b : ℕ, 0 < w ∧ 0 < b ∧ 2^w=4*b ∧ 2*L < 2^w ∧ b ≤ L := by
  obtain ⟨w,hl,hu⟩:=unique_scale hL
  have hw : 2 ≤ w := by
    by_contra hn
    have hw : w=0 ∨ w=1 := by omega
    rcases hw with hw|hw <;> simp [hw] at hl <;> omega
  refine ⟨w,2^(w-2),by omega,pow_pos (by omega) _,?_,hl.1,?_⟩
  · have hh : w=(w-2)+2 := by omega
    nth_rw 1 [hh]
    rw [pow_add]
    norm_num
    omega
  · have hh : 2^w=4*2^(w-2) := by
      have he : w=(w-2)+2 := by omega
      nth_rw 1 [he]
      rw [pow_add]
      norm_num
      omega
    rw [hh] at hl
    omega
end SingleFold.Packed

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable [Fintype Q]
end SingleFold.Counter

namespace SingleFold.Packed
end SingleFold.Packed
namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
end SingleFold.Counter

namespace SingleFold.Packed
end SingleFold.Packed

namespace SingleFold.Counter
open Packed
variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
theorem system_complete (M : Machine Q J) (d : J → ℕ) (h : Halts M d) :
    ∃v,System M d v := by
  obtain ⟨T,hT⟩ := h
  have hc : 0 < baseC Q d+T := by dsimp [baseC]; omega
  obtain ⟨w,b,hw,hb,hB,hlarge,hsmall⟩ := exists_scale hc
  exact ⟨trace M d (2^w) w b T,trace_system M d _ _ _ _ hT rfl hw hb hB hlarge hsmall⟩
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.CounterCompilation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

namespace SingleFold.Compiler.ScalarSF
variable {α ι : Type} {f g : (α → ℕ) → ℕ}
lemma finset_sum (s : Finset ι) (f : ι → (α → ℕ) → ℕ) (h : ∀i∈s,ScalarSF (f i)) :
    ScalarSF (fun z => ∑i∈s,f i z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (α:=α) 0
  | @insert i s hi ih =>
    have hh := (h i (Finset.mem_insert_self _ _)).add (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.sum_insert hi] using hh
lemma sum [Fintype ι] (f : ι → (α → ℕ) → ℕ) (h : ∀i,ScalarSF (f i)) :
    ScalarSF (fun z => ∑i,f i z) := finset_sum Finset.univ f (fun i _=>h i)
lemma bits (hf : ScalarSF f) (hg : ScalarSF g) : SF (fun z=>Binary.Bits (f z) (g z)) := by
  have hv : MapSF (fun z=>![f z,g z]) := MapSF.vector (by intro i; fin_cases i <;> assumption)
  exact hv.pullback Binary.bits
end SingleFold.Compiler.ScalarSF

namespace SingleFold.CounterCompilation
open Compiler Counter
lemma decode_injective {Q J : Type} : Function.Injective (@decode Q J) := by
  intro a b h
  simpa using congrArg encode h

variable {Q J : Type} [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J]
variable (M : Machine Q J)
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma field_sf (i : Var Q J) : ScalarSF (fun z : Input Q J → ℕ => z (.inr i)) := ScalarSF.proj _
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma input_sf (j : J) : ScalarSF (fun z : Input Q J → ℕ => inp z j) := ScalarSF.proj _
omit [DecidableEq Q] [DecidableEq J] in
lemma baseC_sf : ScalarSF (fun z : Input Q J → ℕ => baseC Q (inp z)) :=
  (ScalarSF.const (1+Fintype.card Q)).add (ScalarSF.sum _ input_sf)
omit [Fintype Q] [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma arc_sf (q : Q) (b : Bool) : ScalarSF (fun z : Input Q J → ℕ=>arc M (wit z) q b) := by
  cases hi : M.instr q <;> cases b <;> simp only [arc,hi] <;>
    first | exact field_sf _ | exact ScalarSF.const 0
omit [Fintype J] [DecidableEq J] in
lemma incoming_sf (p : Q) : ScalarSF (fun z : Input Q J → ℕ=>incoming M (wit z) p) := by
  apply ScalarSF.sum
  intro q
  apply ScalarSF.sum
  intro b
  by_cases h : dest M q b=some p
  · simpa only [ite_eq_left h] using arc_sf M q b
  · simpa only [ite_eq_right h] using (ScalarSF.const (α:=Input Q J) 0)
omit [Fintype J] [DecidableEq Q] in
lemma increments_sf (j : J) : ScalarSF (fun z : Input Q J → ℕ=>increments M (wit z) j) := by
  apply ScalarSF.sum
  intro q
  cases hi : M.instr q with
  | halt => exact ScalarSF.const 0
  | inc i p =>
    by_cases h : i=j
    · simpa only [ite_eq_left h,wit,decode,Function.comp_apply] using field_sf (Q:=Q) (J:=J) (.state q)
    · simpa only [ite_eq_right h] using (ScalarSF.const (α:=Input Q J) 0)
  | test i p0 pd => exact ScalarSF.const 0
omit [Fintype J] [DecidableEq Q] in
lemma decrements_sf (j : J) : ScalarSF (fun z : Input Q J → ℕ=>decrements M (wit z) j) := by
  apply ScalarSF.sum
  intro q
  cases hi : M.instr q with
  | halt => exact ScalarSF.const 0
  | inc i p => exact ScalarSF.const 0
  | test i p0 pd =>
    by_cases h : i=j
    · simpa only [ite_eq_left h,wit,decode,Function.comp_apply] using field_sf (Q:=Q) (J:=J) (.decBranch q)
    · simpa only [ite_eq_right h] using (ScalarSF.const (α:=Input Q J) 0)

omit [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma branch_sf : SF (fun z : Input Q J → ℕ=>∀q,match M.instr q with
    | .test _ _ _ => Bits ((wit z).zeroBranch q) ((wit z).state q) ∧
      Bits ((wit z).decBranch q) ((wit z).state q) ∧
      (wit z).zeroBranch q+(wit z).decBranch q=(wit z).state q ∧
      (wit z).zeroBranch q+(wit z).complement q=(wit z).mask
    | _ => (wit z).zeroBranch q=0 ∧ (wit z).decBranch q=0 ∧ (wit z).complement q=0) := by
  apply SF.all
  intro q
  cases hi : M.instr q with
  | halt =>
    exact ((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).eq (ScalarSF.const 0)).and
      (((field_sf (Q:=Q) (J:=J) (.decBranch q)).eq (ScalarSF.const 0)).and ((field_sf (Q:=Q) (J:=J) (.complement q)).eq (ScalarSF.const 0)))
  | inc i p =>
    exact ((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).eq (ScalarSF.const 0)).and
      (((field_sf (Q:=Q) (J:=J) (.decBranch q)).eq (ScalarSF.const 0)).and ((field_sf (Q:=Q) (J:=J) (.complement q)).eq (ScalarSF.const 0)))
  | test i p0 pd =>
    exact ((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).bits (field_sf (Q:=Q) (J:=J) (.state q))).and
      (((field_sf (Q:=Q) (J:=J) (.decBranch q)).bits (field_sf (Q:=Q) (J:=J) (.state q))).and
      ((((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).add (field_sf (Q:=Q) (J:=J) (.decBranch q))).eq (field_sf (Q:=Q) (J:=J) (.state q))).and
      (((field_sf (Q:=Q) (J:=J) (.zeroBranch q)).add (field_sf (Q:=Q) (J:=J) (.complement q))).eq (field_sf (Q:=Q) (J:=J) .mask))))

omit [Fintype J] [DecidableEq Q] [DecidableEq J] in
lemma zero_test_sf : SF (fun z : Input Q J → ℕ=>∀q,match M.instr q with
    | .test j _ _=>Bits ((wit z).counter (some j)) (((wit z).B-1)*(wit z).complement q)
    | _=>True) := by
  have ht : SF (fun _ : Input Q J → ℕ=>True) :=
    (SF.eq (Poly.const 0) (Poly.const 0)).congr (by simp)
  apply SF.all
  intro q
  cases hi : M.instr q with
  | halt => exact ht
  | inc i p => exact ht
  | test j p0 pd =>
    exact (field_sf (Q:=Q) (J:=J) (.counter (some j))).bits
      (((field_sf (Q:=Q) (J:=J) .B).sub (ScalarSF.const 1)).mul (field_sf (Q:=Q) (J:=J) (.complement q)))

lemma system_sf : SF (fun z : Input Q J → ℕ=>System M (inp z) (wit z)) := by
  let a (i : Var Q J) := field_sf i
  let c (k : ℕ) := ScalarSF.const (α:=Input Q J) k
  have hp : SF (fun z : Input Q J → ℕ=>(wit z).B=2^(wit z).w) :=
    ((c 2).powerRel (a .w) (a .B)).congr (by intro z; simp only [le_refl,true_and]; rfl)
  have hb := (a .B).eq ((c 4).mul (a .b))
  have hbound := ((c 2).mul (baseC_sf (Q:=Q) (J:=J))).lt (a .B)
  have hk := (c 0).lt (a .k)
  have hfull := (a .B).powerRel (a .k) (a .H)
  have hlast := ((a .B).mul (a .last)).eq (a .H)
  have hmask := (((a .B).sub (c 1)).mul (a .mask)).eq ((a .H).sub (c 1))
  have hstate := SF.all (fun q=> (a (.state q)).bits (a .mask))
  have hpart := (ScalarSF.sum _ (fun q=>a (.state q))).eq (a .mask)
  have htrans := SF.all (fun q=> (a (.state q)).eq
    ((c (if q=M.start then 1 else 0)).add ((a .B).mul (incoming_sf M q))))
  have hcounter := SF.all (fun j : Option J=>
    ((a (.counter j)).bits ((((c 2).mul (a .b)).sub (c 1)).mul (a .mask))).and
    (((a (.counter j)).eq (((a (.final j)).mul (a .last)).add (a (.rem j)))).and
      ((a (.rem j)).lt (a .last))))
  have hupdate := SF.all (fun j=> ((a (.counter (some j))).add ((a .B).mul (decrements_sf M j))).eq
    ((input_sf j).add ((a .B).mul ((a (.rem (some j))).add (increments_sf M j)))))
  have hclock := ((a (.counter none)).add ((a .B).mul (a .last))).eq
    ((baseC_sf (Q:=Q) (J:=J)).add ((a .B).mul ((a (.rem none)).add (a .mask))))
  have hlower := (a .b).le (a (.final none))
  have hupper := ((c 2).mul (a (.final none))).lt (a .B)
  have hh := hp.and (hb.and (hbound.and (hk.and (hfull.and (hlast.and (hmask.and
    (hstate.and (hpart.and ((branch_sf M).and (htrans.and (hcounter.and (hupdate.and
    ((zero_test_sf M).and (hclock.and (hlower.and hupper)))))))))))))))
  refine hh.congr ?_
  intro z
  constructor
  · rintro ⟨hp,hb,hbound,hk,⟨_,hfull⟩,hlast,hmask,hstate,hpart,hbranch,htrans,hcounter,hupdate,hzero,hclock,hlower,hupper⟩
    exact ⟨hp,hb,hbound,hk,hfull,hlast,hmask,hstate,hpart,hbranch,htrans,hcounter,hupdate,hzero,hclock,hlower,hupper⟩
  · intro h
    exact ⟨h.power,h.base,h.bound,h.length,⟨show 2≤(wit z).B from le_trans (by omega) h.Bfour,h.full⟩,h.last,h.mask,
      h.state_bits,h.partition,h.branch,h.transition,h.counter,h.update,h.zero_test,h.clock,h.scale_lower,h.scale_upper⟩

lemma halts_sf : SF (fun d : J → ℕ=>Counter.Halts M d) := by
  have hh := (system_sf M).ex (fun d v u hv hu=>decode_injective (system_unique hv hu))
  refine hh.congr ?_
  intro d
  constructor
  · rintro ⟨v,hv⟩
    exact ⟨_,hv.haltsAt⟩
  · intro h
    obtain ⟨v,hv⟩:=system_complete M d h
    refine ⟨encode v,?_⟩
    simpa only [inp,wit,Function.comp_def,Sum.elim_inl,Sum.elim_inr,decode_encode] using hv
end SingleFold.CounterCompilation

end OAI

-- ---- from OAI.NumberTheory.SingleFold.MacroMachine ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

namespace SingleFold.Counter
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
end SingleFold.Counter

namespace SingleFold.Macro

section
open Counter StateTransition Relation
variable {Q J : Type}
variable [DecidableEq J]
variable [DecidableEq Q]

omit [DecidableEq Q] in
lemma inc_reg (M : Q → Instr Q J) (start : Q) (s t : State Q) (v : J → ℕ) (a : ℕ) (j : J)
    (hi : compileInstr M s=.inc (.inl j) t) :
    Counter.step (compile M start) (cfg s v a)=some (cfg t (Function.update v j (v j+1)) a) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,Sum.elim_inl]
  congr 1
  congr 1
  funext i
  cases i <;> simp [Function.update_apply]
omit [DecidableEq Q] in
lemma inc_scratch (M : Q → Instr Q J) (start : Q) (s t : State Q) (v : J → ℕ) (a : ℕ)
    (hi : compileInstr M s=.inc scratch t) :
    Counter.step (compile M start) (cfg s v a)=some (cfg t v (a+1)) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,scratch,Sum.elim_inr,Bool.false_eq_true,ite_false]
  congr 1
  congr 1
  funext i
  rcases i with j|b
  · simp
  · cases b <;> simp
omit [DecidableEq Q] in
lemma test_reg (M : Q → Instr Q J) (start : Q) (s t u : State Q) (v : J → ℕ) (a : ℕ) (j : J)
    (hi : compileInstr M s=.test (.inl j) t u) :
    Counter.step (compile M start) (cfg s v a)=
      some (if v j=0 then cfg t v a else cfg u (Function.update v j (v j-1)) a) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,Sum.elim_inl]
  by_cases h : v j=0
  · simp [h]
  · simp only [h, ite_false]; congr 1; congr 1; funext i; cases i <;> simp [Function.update_apply]
omit [DecidableEq Q] in
lemma test_scratch (M : Q → Instr Q J) (start : Q) (s t u : State Q) (v : J → ℕ) (a : ℕ)
    (hi : compileInstr M s=.test scratch t u) :
    Counter.step (compile M start) (cfg s v a)=
      some (if a=0 then cfg t v a else cfg u v (a-1)) := by
  simp only [Counter.step,compile,cfg,hi,Counter.next,scratch,Sum.elim_inr,Bool.false_eq_true,ite_false]
  split_ifs
  · rfl
  · congr 1; congr 1; funext i
    rcases i with j|b
    · simp
    · cases b <;> simp
omit [DecidableEq Q] in
lemma goto (M : Q → Instr Q J) (start : Q) (s t : State Q) (v : J → ℕ) (a : ℕ)
    (hi : compileInstr M s=go t) :
    Counter.step (compile M start) (cfg s v a)=some (cfg t v a) := by
  simp [Counter.step,compile,cfg,hi,go,Counter.next,zeroReg]
end

section
open Counter StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
variable (M : Q → Instr Q J) (start : Q)
local notation "F" => Counter.step (compile M start)
omit [DecidableEq Q] in
lemma prepend {c d e : Counter.Cfg (State Q) (Reg J)}
    (ht : Reaches₁ F d e) (h : F c=some d) : Reaches₁ F c e :=
  TransGen.head (r:=fun c d=>d∈F c) h ht
omit [DecidableEq Q] in
lemma inc_at (s t : State Q) (v : J → ℕ) (a n : ℕ) (j : J)
    (hi : compileInstr M s=.inc (.inl j) t) :
    F (cfg s (Function.update v j n) a)=some (cfg t (Function.update v j (n+1)) a) := by
  simpa using inc_reg M start s t (Function.update v j n) a j hi
omit [DecidableEq Q] in
lemma test_at_zero (s t u : State Q) (v : J → ℕ) (a : ℕ) (j : J)
    (hi : compileInstr M s=.test (.inl j) t u) :
    F (cfg s (Function.update v j 0) a)=some (cfg t (Function.update v j 0) a) := by
  simpa using test_reg M start s t u (Function.update v j 0) a j hi
omit [DecidableEq Q] in
lemma test_at_succ (s t u : State Q) (v : J → ℕ) (a n : ℕ) (j : J)
    (hi : compileInstr M s=.test (.inl j) t u) :
    F (cfg s (Function.update v j (n+1)) a)=some (cfg u (Function.update v j n) a) := by
  simpa using test_reg M start s t u (Function.update v j (n+1)) a j hi

omit [DecidableEq Q] in
lemma grow_loop (q : Q) (i : Fin 5) (v : J → ℕ) (a : ℕ) :
    Reaches₁ F (cfg (.grow q i) v a) (cfg (.main q) v (a+(5-i.val))) := by
  induction i using Fin.reverseInduction generalizing a with
  | last =>
    exact TransGen.single (by simpa using inc_scratch M start (.grow q 4) (.main q) v a rfl)
  | cast i ih =>
    have hi : i.val < 4 := i.isLt
    have hs : succ5 i.castSucc=i.succ := by ext; simp [succ5]; omega
    have hh : compileInstr M (.grow q i.castSucc)=.inc scratch (.grow q i.succ) := by
      simp only [compileInstr,Fin.val_castSucc]
      rw [ite_eq_right (by omega),hs]
    have he := inc_scratch M start (.grow q i.castSucc) (.grow q i.succ) v a hh
    have ht := prepend M start (ih (a+1)) he
    convert ht using 1 ; congr 1 ; simp only [Fin.val_castSucc,Fin.val_succ] ; omega

omit [DecidableEq Q] in
lemma multiply_loop (q : Q) (j : J) (e : Fin 5) (p : Q) (hm : M q=.muladd j e p)
    (v : J → ℕ) (n a : ℕ) :
    Reaches₁ F (cfg (.main q) (Function.update v j n) a)
      (cfg (.copy q 0) (Function.update v j 0) (a+5*n)) := by
  induction n generalizing a with
  | zero =>
    apply TransGen.single
    simpa using test_at_zero M start (.main q) (.copy q 0) (.grow q 0) v a j (by simp [compileInstr,hm])
  | succ n ih =>
    have h1 := test_at_succ M start (.main q) (.copy q 0) (.grow q 0) v a n j (by simp [compileInstr,hm])
    have h2 := grow_loop M start q 0 (Function.update v j n) a
    have h3 := prepend M start (h2.trans (ih (a+5))) h1
    convert h3 using 1 ; congr 1 ; omega

omit [DecidableEq Q] in
lemma copy_loop (q : Q) (j : J) (r : Fin 5)
    (hm : (∃e p,M q=.muladd j e p) ∨ (∃b p,M q=.div j b p))
    (v : J → ℕ) (n a : ℕ) :
    Reaches₁ F (cfg (.copy q r) (Function.update v j n) a)
      (cfg (finish M q r) (Function.update v j (n+a)) 0) := by
  induction a generalizing n with
  | zero =>
    apply TransGen.single
    simpa using test_scratch M start (.copy q r) (finish M q r) (.copyInc q r) (Function.update v j n) 0 rfl
  | succ a ih =>
    have h1 := test_scratch M start (.copy q r) (finish M q r) (.copyInc q r) (Function.update v j n) (a+1) rfl
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, Nat.add_sub_cancel] at h1
    have hh : compileInstr M (.copyInc q r)=.inc (.inl j) (.copy q r) := by
      rcases hm with ⟨e,p,h⟩|⟨b,p,h⟩ <;> simp [compileInstr,h]
    have h2 := inc_at M start (.copyInc q r) (.copy q r) v a n j hh
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using prepend M start (prepend M start (ih (n+1)) h2) h1

omit [DecidableEq Q] in
lemma add_loop (q : Q) (j : J) (e : Fin 5) (p : Q) (hm : M q=.muladd j e p)
    (i : Fin 5) (hi : i.val ≤ e.val) (v : J → ℕ) (n a : ℕ) :
    Reaches₁ F (cfg (.add q i) (Function.update v j n) a)
      (cfg (.main p) (Function.update v j (n+(e.val-i.val))) a) := by
  induction i using Fin.reverseInduction generalizing n with
  | last =>
    have hh : e.val=4 := by have := e.isLt; simp only [Fin.val_last] at hi; omega
    apply TransGen.single
    simpa [hh] using goto M start (.add q 4) (.main p) (Function.update v j n) a (by simp [compileInstr,hm,hh])
  | cast i ih =>
    simp only [Fin.val_castSucc] at hi
    by_cases he : i.val=e.val
    · apply TransGen.single
      simpa [he] using goto M start (.add q i.castSucc) (.main p) (Function.update v j n) a (by simp [compileInstr,hm,he])
    · have hs : succ5 i.castSucc=i.succ := by ext; simp [succ5]; have := i.isLt; omega
      have h1 := inc_at M start (.add q i.castSucc) (.add q i.succ) v a n j (by
        simp only [compileInstr,hm,Fin.val_castSucc]; rw [ite_eq_left (by omega),hs])
      have h2 := prepend M start (ih (by simp only [Fin.val_succ]; omega) (n+1)) h1
      have har : n+(e.val-i.val)=(n+1)+(e.val-(i.val+1)) := by omega
      simpa only [Fin.val_castSucc,Fin.val_succ,har] using h2
end

open Counter StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
lemma mod5_self (b : Bool) (r : Fin 5) (hr : r.val<radix b) : mod5 b r.val=r :=
  Fin.ext (Nat.mod_eq_of_lt hr)
variable (M : Q → Instr Q J) (start : Q)
local notation "F" => Counter.step (compile M start)
omit [DecidableEq Q] in
lemma quotient_loop (q : Q) (j : J) (b : Bool) (p : Fin 5 → Q) (hm : M q=.div j b p)
    (v : J → ℕ) (n : ℕ) (r : Fin 5) (hr : r.val<radix b) (a : ℕ) :
    Reaches₁ F (cfg (.quotient q r) (Function.update v j n) a)
      (cfg (.copy q (mod5 b (n+r.val))) (Function.update v j 0) (a+(n+r.val)/radix b)) := by
  induction n generalizing r a with
  | zero =>
    apply TransGen.single
    simpa [mod5_self b r hr, Nat.div_eq_of_lt hr] using test_at_zero M start (.quotient q r) (.copy q r)
      (if r.val+1=radix b then .carry q else .quotient q (succ5 r)) v a j (by simp [compileInstr,hm])
  | succ n ih =>
    have h1 := test_at_succ M start (.quotient q r) (.copy q r)
      (if r.val+1=radix b then .carry q else .quotient q (succ5 r)) v a n j (by simp [compileInstr,hm])
    by_cases he : r.val+1=radix b
    · simp only [he,ite_eq_left] at h1
      have h2 := inc_scratch M start (.carry q) (.quotient q 0) (Function.update v j n) a rfl
      have h3 := prepend M start (prepend M start (ih 0 (radix_pos b) (a+1)) h2) h1
      have har : n+1+r.val=n+radix b := by omega
      simpa [har,mod5,radix_pos b,Nat.add_div_right, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3
    · have hs : (succ5 r).val=r.val+1 := by
        apply Nat.mod_eq_of_lt
        have := radix_le b
        omega
      simp only [he,ite_false] at h1
      have h3 := prepend M start (ih (succ5 r) (by rw [hs]; omega) a) h1
      simpa only [hs, Nat.succ_eq_add_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h3

omit [DecidableEq Q] in
lemma simulate (q : Q) (v : J → ℕ) :
    Reaches₁ F (cfg (.main q) v 0) (encode (next M q v)) := by
  cases hm : M q with
  | halt =>
    apply TransGen.single
    simpa [next,hm,encode] using goto M start (.main q) .halt v 0 (by simp [compileInstr,hm])
  | goto p =>
    apply TransGen.single
    simpa [next,hm,encode] using goto M start (.main q) (.main p) v 0 (by simp [compileInstr,hm])
  | inc j p =>
    apply TransGen.single
    simpa [next,hm,encode] using inc_reg M start (.main q) (.main p) v 0 j (by simp [compileInstr,hm])
  | test j pz pp =>
    have h1 := test_reg M start (.main q) (.main pz) (.restore q) v 0 j (by simp [compileInstr,hm])
    by_cases hz : v j=0
    · apply TransGen.single
      simpa [next,hm,encode,hz] using h1
    · simp only [hz,ite_false] at h1
      have h2 := inc_at M start (.restore q) (.main pp) v 0 (v j-1) j (by simp [compileInstr,hm])
      have har : v j-1+1=v j := by omega
      have ht : Reaches₁ F (cfg (.restore q) (Function.update v j (v j-1)) 0) (cfg (.main pp) v 0) :=
        TransGen.single (by simpa [har] using h2)
      simpa [next,hm,encode,hz] using prepend M start ht h1
  | muladd j e p =>
    have h1 := multiply_loop M start q j e p hm v (v j) 0
    have h2 := copy_loop M start q j 0 (Or.inl ⟨e,p,hm⟩) v 0 (5*v j)
    have h3 := add_loop M start q j e p hm 0 (Nat.zero_le _) v (5*v j) 0
    simp only [Nat.zero_add] at h1
    simp only [finish,hm,Nat.zero_add] at h2
    simp only [Fin.val_zero,Nat.sub_zero] at h3
    have ht := (h1.trans h2).trans h3
    simpa [next,hm,encode,Reaches₁] using ht
  | div j b p =>
    have h1 := goto M start (.main q) (.quotient q 0) v 0 (by simp [compileInstr,hm])
    have h2 := quotient_loop M start q j b p hm v (v j) 0 (radix_pos b) 0
    have h3 := copy_loop M start q j (mod5 b (v j)) (Or.inr ⟨b,p,hm⟩) v 0 (v j/radix b)
    simp only [Fin.val_zero,Nat.add_zero,Nat.zero_add,Function.update_eq_self] at h2
    simp only [finish,hm,Nat.zero_add] at h3
    simpa [next,hm,encode,mod5] using prepend M start (h2.trans h3) h1

omit [DecidableEq Q] in
lemma respects : Respects (step M) F (fun c d=>encode c=d) := by
  apply fun_respects.mpr
  intro c
  rcases c with ⟨label,v⟩
  cases label with
  | none => simp [step,encode,FRespects,Counter.step,compile,compileInstr,cfg]
  | some q => exact simulate M start q v
omit [DecidableEq Q] in
lemma eval_dom (c : Cfg Q J) :
    (eval F (encode c)).Dom ↔ (eval (step M) c).Dom :=
  tr_eval_dom (respects M start) rfl
end SingleFold.Macro

namespace SingleFold.Counter
open StateTransition Relation
variable {Q J : Type} [DecidableEq Q] [DecidableEq J]
end SingleFold.Counter

end OAI

-- ---- from OAI.NumberTheory.SingleFold.TuringSimulation ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section

namespace SingleFold.TM2Macro

section
open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
lemma digit_pos (s : Symbol) : 0 < (digit s).val := by cases s <;> decide

lemma pack_div (l : List Symbol) : pack l/5=pack l.tail := by
  cases l with
  | nil => rfl
  | cons s l => simp [Nat.mul_add_div, Nat.div_eq_of_lt (digit s).isLt]
lemma pack_mod (l : List Symbol) : mod5 false (pack l)=l.head?.elim 0 digit := by
  cases l with
  | nil => rfl
  | cons s l => apply Fin.ext; simp [mod5,Macro.radix, Nat.mod_eq_of_lt (digit s).isLt]
variable {n : ℕ} {Λ : Type}
lemma respects (M : Λ → Stmt Λ) (initial : Λ) (x : Fin n → ℕ) :
    Respects (TM2.step M) (Macro.step (program M initial)) (fun c d=>encode M c x=d) := by
  apply fun_respects.mpr
  rintro ⟨l,v,S⟩
  cases l with
  | none => rfl
  | some l => exact stepAux_reaches M initial (M l) v S x
lemma eval_dom (M : Λ → Stmt Λ) (initial : Λ) (c : TM2.Cfg (fun _ : Stack=>Symbol) Λ Store) (x : Fin n → ℕ) :
    (eval (Macro.step (program M initial)) (encode M c x)).Dom ↔ (eval (TM2.step M) c).Dom :=
  tr_eval_dom (respects M initial x) rfl
end

section
open Turing Turing.PartrecToTM2 StateTransition Relation
lemma trNat_posNum (p : PosNum) : trNat (p:ℕ)=trPosNum p := by
  simp [trNat,trNum]
lemma trNat_div (a : ℕ) (ha : a≠0) : trNat a=(if a%2=0 then Γ'.bit0 else Γ'.bit1)::trNat (a/2) := by
  have H (m : Num) (hm : (m:ℕ)≠0) : trNat (m:ℕ)=(if (m:ℕ)%2=0 then Γ'.bit0 else Γ'.bit1)::trNat ((m:ℕ)/2) := by
    cases m with
    | zero => exact (hm rfl).elim
    | pos p =>
      change trNat (p:ℕ)=_
      rw [trNat_posNum]
      cases p with
      | one => simp [trPosNum]
      | bit0 p =>
        have he : ((p:ℕ)+(p:ℕ))%2=0 := by omega
        have hd : ((p:ℕ)+(p:ℕ))/2=(p:ℕ) := by omega
        simp only [Num.cast_pos,PosNum.cast_bit0,he,ite_true,hd,trPosNum,trNat_posNum]
      | bit1 p =>
        have he : ((p:ℕ)+(p:ℕ)+1)%2≠0 := by omega
        have hd : ((p:ℕ)+(p:ℕ)+1)/2=(p:ℕ) := by omega
        simp only [Num.cast_pos,PosNum.cast_bit1,he,ite_false,hd,trPosNum,trNat_posNum]
  simpa only [Num.to_of_nat] using H (a:Num) (by simpa only [Num.to_of_nat] using ha)

open Turing Turing.PartrecToTM2 StateTransition Relation
open Macro (mod5)
variable {n : ℕ} {Λ : Type}
lemma initValues_update_main (L R L' : List Symbol) (x : Fin n → ℕ) :
    Function.update (initValues L R x) (.inl .main) (pack L')=initValues L' R x := by
  funext j
  rcases j with k|i
  · cases k <;> simp [initValues,values,K'.elim]
  · simp [initValues,values]
lemma initValues_update_rev (L R R' : List Symbol) (x : Fin n → ℕ) :
    Function.update (initValues L R x) (.inl .rev) (pack R')=initValues L R' x := by
  funext j
  rcases j with k|i
  · cases k <;> simp [initValues,values,K'.elim]
  · simp [initValues,values]
lemma initValues_update_input (L R : List Symbol) (x : Fin n → ℕ) (i : Fin n) (a : ℕ) :
    Function.update (initValues L R x) (.inr i) a=initValues L R (Function.update x i a) := by
  funext j
  rcases j with k|j <;> simp [initValues,values,Function.update_apply]
variable (M : Λ → Stmt Λ) (initial : Λ)
local notation "F" => Macro.step (program M initial)
lemma prepend {c d e : Macro.Cfg (Label n Λ) (Reg n)} (ht : Reaches₁ F d e) (h : F c=some d) : Reaches₁ F c e :=
  TransGen.head (r:=fun c d=>d∈F c) h ht

lemma reverse_loop (i : Fin n) (L R : List Symbol) (x : Fin n → ℕ) :
    Reaches₁ F (initCfg (.reverse i) L R x) (initCfg (.start i.castSucc) (R.reverse++L) [] x) := by
  induction R generalizing L with
  | nil =>
    apply TransGen.single
    have hv : Function.update (initValues L [] x) (.inl .rev) 0=initValues L [] x :=
      initValues_update_rev L [] [] x
    simp [Macro.step,initCfg,Macro.next,program,Macro.radix,hv]
  | cons s R ih =>
    have h1 : F (initCfg (.reverse i) L (s::R) x)=some (initCfg (.pushRev i (digit s)) L R x) := by
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (if (mod5 false (pack (s::R))).val=0 then .start i.castSucc else .pushRev i (mod5 false (pack (s::R))))) (Function.update (initValues L (s::R) x) (.inl .rev) (pack (s::R)/5)))=some _
      rw [show mod5 false (pack (s::R))=digit s from pack_mod _,
        show pack (s::R)/5=pack R from pack_div _, initValues_update_rev,
        ite_eq_right (Nat.ne_of_gt (digit_pos s))]
      rfl
    have h2 : F (initCfg (.pushRev i (digit s)) L R x)=some (initCfg (.reverse i) (s::L) R x) := by
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.reverse i)) (Function.update (initValues L R x) (.inl .main) (pack (s::L))))=some _
      rw [initValues_update_main]; rfl
    simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using prepend M initial (prepend M initial (ih (s::L)) h2) h1

lemma divide_loop (i : Fin n) (L R : List Symbol) (x : Fin n → ℕ) (a : ℕ) :
    Reaches₁ F (initCfg (.divide i) L R (Function.update x i a))
      (initCfg (.reverse i) L ((trNat a).reverse++R) (Function.update x i 0)) := by
  induction a using Nat.strong_induction_on generalizing R with
  | h a ih =>
    have hx : Function.update x i a i=a := Function.update_self _ _ _
    by_cases ha : a=0
    · subst a
      apply TransGen.single
      change some (Macro.Cfg.mk (Q:=Label n Λ) (some (if Function.update x i 0 i=0 then .reverse i else .bit i)) (initValues L R (Function.update x i 0)))=some _
      rw [Function.update_self,ite_eq_left rfl]
      simp only [trNat_zero,List.reverse_nil,List.nil_append,initCfg]
    · let s : Symbol := if a%2=0 then .bit0 else .bit1
      have h1 : F (initCfg (.divide i) L R (Function.update x i a))=some (initCfg (.bit i) L R (Function.update x i a)) := by
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (if Function.update x i a i=0 then .reverse i else .bit i)) (initValues L R (Function.update x i a)))=some _
        rw [hx,ite_eq_right ha]; rfl
      have h2 : F (initCfg (.bit i) L R (Function.update x i a))=some (initCfg (.pushBit i (mod5 true a)) L R (Function.update x i (a/2))) := by
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.pushBit i (mod5 true (Function.update x i a i)))) (Function.update (initValues L R (Function.update x i a)) (.inr i) (Function.update x i a i/2)))=some _
        rw [hx,initValues_update_input,Function.update_idem]; rfl
      have h3 : F (initCfg (.pushBit i (mod5 true a)) L R (Function.update x i (a/2)))=some (initCfg (.divide i) L (s::R) (Function.update x i (a/2))) := by
        change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.divide i)) (Function.update (initValues L R (Function.update x i (a/2))) (.inl .rev) (pack (s::R))))=some _
        rw [initValues_update_rev]; rfl
      have ht := prepend M initial (prepend M initial (prepend M initial (ih (a/2) (Nat.div_lt_self (Nat.pos_of_ne_zero ha) (by omega)) (s::R)) h3) h2) h1
      simpa only [trNat_div a ha,List.reverse_cons,List.append_assoc,List.singleton_append] using ht

lemma one_input (i : Fin n) (L : List Symbol) (x : Fin n → ℕ) :
    Reaches₁ F (initCfg (.start i.succ) L [] x)
      (initCfg (.start i.castSucc) (trNat (x i)++Γ'.cons::L) [] (Function.update x i 0)) := by
  have h1 : F (initCfg (.start i.succ) L [] x)=some (initCfg (.divide i) (Γ'.cons::L) [] x) := by
    simp only [Macro.step,initCfg,Macro.next,program,Option.map_some,Fin.val_succ,
      Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,dite_false,Nat.add_sub_cancel,initValues_main]
    change some (Macro.Cfg.mk (Q:=Label n Λ) (some (.divide i)) (Function.update (initValues L [] x) (.inl .main) (pack (Γ'.cons::L))))=some _
    rw [initValues_update_main]
  have h2 := divide_loop M initial i (Γ'.cons::L) [] x (x i)
  simp only [Function.update_eq_self,List.append_nil] at h2
  have h3 := reverse_loop M initial i (Γ'.cons::L) (trNat (x i)).reverse (Function.update x i 0)
  simp only [List.reverse_reverse] at h3
  exact prepend M initial (h2.trans h3) h1
end

open Turing Turing.PartrecToTM2 StateTransition Relation
variable {n : ℕ} {Λ : Type}
lemma prefix_succ (x : Fin n → ℕ) (k : ℕ) (hk : k+1≤n) :
    inputPrefix x (k+1) hk=inputPrefix x k (by omega)++[x ⟨k,by omega⟩] := by
  unfold inputPrefix
  rw [List.ofFn_succ',List.concat_eq_append]
  rfl
lemma prefix_update (x : Fin n → ℕ) (k : ℕ) (hk : k<n) :
    inputPrefix (Function.update x ⟨k,hk⟩ 0) k (by omega)=inputPrefix x k (by omega) := by
  apply congrArg List.ofFn
  funext j
  exact Function.update_of_ne (by intro he; have hh:=congrArg Fin.val he; exact Nat.ne_of_lt j.isLt hh) _ _
lemma clearPrefix_update (x : Fin n → ℕ) (k : ℕ) (hk : k<n) :
    clearPrefix (Function.update x ⟨k,hk⟩ 0) k=clearPrefix x (k+1) := by
  funext j
  by_cases h : j.val<k
  · simp [clearPrefix,h,show j.val<k+1 by omega]
  · by_cases he : j.val=k
    · have hej : j=⟨k,hk⟩ := Fin.ext he
      simp [clearPrefix,hej]
    · have hej : j≠⟨k,hk⟩ := fun hh=>he (congrArg Fin.val hh)
      simp [clearPrefix,h,show ¬j.val<k+1 by omega,Function.update_of_ne hej]
lemma trList_append (L R : List ℕ) : trList (L++R)=trList L++trList R := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.cons_append,trList,ih,List.append_assoc,List.cons_append]
variable (M : Λ → Stmt Λ) (initial : Λ)
local notation "F" => Macro.step (program M initial)
lemma init_loop (k : ℕ) (hk : k≤n) (L : List Symbol) (x : Fin n → ℕ) :
    Reaches F (initCfg (.start ⟨k,by omega⟩) L [] x)
      (initCfg (.start 0) (trList (inputPrefix x k hk)++L) [] (clearPrefix x k)) := by
  induction k generalizing L x with
  | zero =>
    have hc : clearPrefix x 0=x := by funext j; simp [clearPrefix]
    rw [hc]
    exact ReflTransGen.refl
  | succ k ih =>
    have ht := (one_input M initial (⟨k,by omega⟩:Fin n) L x).to_reflTransGen
    have hs := ih (by omega) (trNat (x ⟨k,by omega⟩)++Γ'.cons::L) (Function.update x ⟨k,by omega⟩ 0)
    rw [prefix_update,clearPrefix_update] at hs
    have hh := ht.trans hs
    change ReflTransGen (fun c d=>d∈F c) _ _
    simp only [prefix_succ,trList_append,trList,List.append_assoc,List.cons_append,List.nil_append]
    exact hh

lemma initialize_reaches (x : Fin n → ℕ) :
    Reaches₁ F (initCfg (.start (Fin.last n)) [] [] x)
      (codeCfg (M initial) none (K'.elim (trList (List.ofFn x)) [] [] []) (fun _=>0)) := by
  have ht := init_loop M initial n le_rfl [] x
  have hp : inputPrefix x n le_rfl=List.ofFn x := rfl
  have hc : clearPrefix x n=(fun _=>0) := by funext j; simp [clearPrefix,j.isLt]
  rw [hp,hc,List.append_nil] at ht
  apply TransGen.tail' ht
  change some (Macro.next (program M initial) (.start 0) _)=some _
  simp only [Macro.next,program,Fin.val_zero]
  rfl
end SingleFold.TM2Macro

namespace SingleFold.Macro
open StateTransition Relation
open scoped Classical
variable {Q Q' J : Type} [DecidableEq J]
omit [DecidableEq J] in
lemma instr_retract (p : Q → Prop) (q₀ : {q // p q}) (i : Instr Q J) (hi : i.Within p) :
    Instr.map Subtype.val (Instr.map (retract p q₀) i)=i := by
  cases i <;> simp_all [Instr.map,Instr.Within,retract,Function.comp_def]
lemma cfg_next_map (f : Q → Q') (M : Q → Instr Q J) (q : Q) (v : J → ℕ) :
    Cfg.map f (next M q v)=next (fun _=>Instr.map f (M q)) (f q) v := by
  cases h : M q <;> simp only [next,h,Instr.map,Cfg.map]
  case test j p r => split <;> rfl
  all_goals rfl
lemma restrict_next (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q})
    (hM : ∀ q,p q → (M q).Within p) (q : {q // p q}) (v : J → ℕ) :
    Cfg.map Subtype.val (next (restrict M p q₀) q v)=next M q.val v := by
  rw [cfg_next_map]
  have he : Instr.map Subtype.val (restrict M p q₀ q)=M q.val := instr_retract p q₀ _ (hM q q.property)
  rw [he]
  rfl
lemma restrict_respects (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q})
    (hM : ∀ q,p q → (M q).Within p) :
    Respects (step (restrict M p q₀)) (step M) (fun c d=>Cfg.map Subtype.val c=d) := by
  apply fun_respects.mpr
  rintro ⟨l,v⟩
  cases l with
  | none => rfl
  | some q =>
    apply TransGen.single
    change some (next M q.val v)=some (Cfg.map Subtype.val (next (restrict M p q₀) q v))
    rw [restrict_next M p q₀ hM]
lemma restrict_eval_dom (M : Q → Instr Q J) (p : Q → Prop) (q₀ : {q // p q})
    (hM : ∀ q,p q → (M q).Within p) (c : Cfg {q // p q} J) :
    (eval (step (restrict M p q₀)) c).Dom ↔ (eval (step M) (Cfg.map Subtype.val c)).Dom :=
  (tr_eval_dom (restrict_respects M p q₀ hM) rfl).symm
end SingleFold.Macro

end

end OAI

-- ---- from OAI.NumberTheory.SingleFold.RecursiveEnumeration ----
namespace OAI

noncomputable section

namespace SingleFold.TM2Macro
open Turing Turing.PartrecToTM2 StateTransition Relation
open scoped Classical
variable {n : ℕ} {Λ : Type}
lemma program_within (M : Λ → Stmt Λ) (initial : Λ) (A : Finset (Stmt Λ))
    (hinit : M initial∈A) (hsub : ∀ q∈A,TM2.stmts₁ q⊆A)
    (hgoto : ∀ f, (TM2.Stmt.goto f : Stmt Λ)∈A → ∀ v,M (f v)∈A) :
    ∀ q : Label n Λ,Good A q → (program M initial q).Within (Good A) := by
  intro q hq
  cases q with
  | code q v =>
    change q∈A at hq
    have hs := hsub q hq
    cases q with
    | push k f q => exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | peek k f q => intro d; exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | pop k f q => intro d; exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | load f q => exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | branch f q r =>
      change (if f v then q else r)∈A
      split <;> exact hs (by simp [TM2.stmts₁,TM2.stmts₁_self])
    | goto f => exact hgoto f hq v
    | halt => trivial
  | restore k d q v => dsimp only [program]; split <;> exact hq
  | start i => simp only [program]; split <;> simp_all [Macro.Instr.Within,Good]
  | divide i => exact ⟨trivial,trivial⟩
  | bit i => intro d; trivial
  | pushBit i d => trivial
  | reverse i => intro d; change Good A (if d.val=0 then _ else _); split <;> trivial
  | pushRev i d => trivial

lemma statements_self (M : Λ → Stmt Λ) (S : Finset Λ) {l : Λ} (hl : l∈S) : M l∈statements M S :=
  Finset.mem_biUnion.mpr ⟨l,hl,TM2.stmts₁_self⟩
lemma statements_sub (M : Λ → Stmt Λ) (S : Finset Λ) (q : Stmt Λ) (hq : q∈statements M S) :
    TM2.stmts₁ q⊆statements M S := by
  obtain ⟨l,hl,hq⟩:=Finset.mem_biUnion.mp hq
  intro r hr
  exact Finset.mem_biUnion.mpr ⟨l,hl,TM2.stmts₁_trans hq hr⟩
lemma statements_goto (M : Λ → Stmt Λ) (S : Finset Λ) (hS : ∀ l∈S,TM2.SupportsStmt S (M l))
    (f : Store → Λ) (hf : (TM2.Stmt.goto f : Stmt Λ)∈statements M S) (v : Store) :
    M (f v)∈statements M S := by
  obtain ⟨l,hl,hf⟩:=Finset.mem_biUnion.mp hf
  exact statements_self M S (TM2.stmts₁_supportsStmt_mono hf (hS l hl) v)

lemma counterInput_eq (a : Fin n → ℕ) : counterInput a=Sum.elim (initValues [] [] a) (fun b=>if b then 0 else 0) := by
  funext j
  rcases j with (k|i)|b
  · cases k <;> rfl
  · rfl
  · cases b <;> rfl
lemma counter_halts (M : Λ → Stmt Λ) (initial : Λ) (S : Finset Λ)
    (hini : initial∈S) (hS : ∀ l∈S,TM2.SupportsStmt S (M l)) (a : Fin n → ℕ) :
    Counter.Halts (counterProgram M initial S) (counterInput a) ↔
      (eval (TM2.step M) ⟨some initial,none,K'.elim (trList (List.ofFn a)) [] [] []⟩).Dom := by
  let c : Macro.Cfg (FiniteState n M S) (Reg n) := ⟨some (finStart M S),initValues [] [] a⟩
  have hstep := program_within M initial (statements M S) (statements_self M S hini)
    (statements_sub M S) (statements_goto M S hS) (n:=n)
  have henc : Macro.encode c=⟨(counterProgram M initial S).start,counterInput a⟩ := by
    rw [counterInput_eq]
    rfl
  have hfin := Macro.restrict_eval_dom (program M initial) (Good (statements M S)) (finStart M S) hstep c
  have htrace := reaches_eval (initialize_reaches M initial a).to_reflTransGen
  have hsim := eval_dom M initial ⟨some initial,none,K'.elim (trList (List.ofFn a)) [] [] []⟩ (fun _ : Fin n=>0)
  calc
    Counter.Halts (counterProgram M initial S) (counterInput a) ↔
        (eval (Counter.step (counterProgram M initial S)) (Macro.encode c)).Dom := by
          rw [henc]; exact (Counter.eval_dom_iff_halts _ _).symm
    _ ↔ (eval (Macro.step (finProgram M initial S)) c).Dom := Macro.eval_dom _ _ c
    _ ↔ (eval (Macro.step (program M initial)) (initCfg (.start (Fin.last n)) [] [] a)).Dom := hfin
    _ ↔ (eval (Macro.step (program M initial))
      (codeCfg (M initial) none (K'.elim (trList (List.ofFn a)) [] [] []) (fun _=>0))).Dom := by rw [htrace]
    _ ↔ _ := hsim

lemma exists_code {p : (Fin n → ℕ) → Prop} (hp : REPred p) :
    ∃ c : ToPartrec.Code,∀a,(ToPartrec.Code.eval c (List.ofFn a)).Dom ↔ p a := by
  let f (v : List.Vector ℕ n) : Part ℕ :=
    (Part.assert (p v.get) (fun _=>Part.some ())).map (fun _=>0)
  have hf : Partrec f := (hp.comp Primrec.vector_get'.to_comp).map (Computable.const 0).to₂
  obtain ⟨c,hc⟩:=ToPartrec.Code.exists_code (Nat.Partrec'.of_part hf)
  refine ⟨c,fun a=>?_⟩
  rw [←List.Vector.toList_ofFn a]
  change (ToPartrec.Code.eval c (List.Vector.ofFn a).val).Dom ↔p a
  rw [hc]
  have hg : (List.Vector.ofFn a).get=a := funext (List.Vector.get_ofFn a)
  change (∃ _ : p (List.Vector.ofFn a).get, True) ↔p a
  rw [hg]
  simp

theorem exists_counter {p : (Fin n → ℕ) → Prop} (hp : REPred p) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : DecidableEq Q) (M : Counter.Machine Q (Macro.Reg (Reg n))),
      ∀a, p a ↔ Counter.Halts M (counterInput a) := by
  obtain ⟨c,hc⟩:=exists_code hp
  let initial := trNormal c Cont'.halt
  let S := codeSupp c Cont'.halt
  have hS := tr_supports c Cont'.halt
  refine ⟨Macro.State (FiniteState n tr S),inferInstance,inferInstance,counterProgram tr initial S,fun a=>?_⟩
  rw [counter_halts tr initial S hS.1 hS.2]
  change p a ↔ (eval (TM2.step tr) (init c (List.ofFn a))).Dom
  rw [PartrecToTM2.tr_eval]
  exact (hc a).symm
end SingleFold.TM2Macro

end

end OAI

-- ---- from OAI.NumberTheory.SingleFold.Main ----
namespace OAI

namespace SingleFold
open Compiler

theorem recursively_enumerable_sf {n : ℕ} {p : (Fin n → ℕ) → Prop} (hp : REPred p) : SF p := by
  obtain ⟨Q,hQ,hD,M,hM⟩:=TM2Macro.exists_counter hp
  let := hQ
  let := hD
  have hc := CounterCompilation.halts_sf M
  have hi : MapSF (TM2Macro.counterInput (n:=n)) := by
    apply MapSF.vector
    intro j
    cases hs : TM2Macro.inputSlot j with
    | none => simpa only [TM2Macro.counterInput,hs,Option.elim_none] using (ScalarSF.const (α:=Fin n) 0)
    | some i => simpa only [TM2Macro.counterInput,hs,Option.elim_some] using ScalarSF.proj i
  exact (hi.pullback hc).congr (fun a=>(hM a).symm)

theorem main : MainStatement := by
  intro n _ S hS
  obtain ⟨r⟩:=recursively_enumerable_sf hS
  obtain ⟨m,hm,P,hP,hU⟩:=export_polynomial r
  exact ⟨m,hm,P,fun a=>⟨hP a,hU a⟩⟩
end SingleFold

end OAI

-- ---- mission target ----
open OAI OAI.SingleFold
open Compiler

namespace OAI
namespace SingleFold
theorem _root_.solution : MainStatement := by
  first
    | exact OAI.SingleFold.main
    | (apply OAI.SingleFold.main <;> assumption)
    | (intros; apply OAI.SingleFold.main <;> assumption)
end SingleFold
end OAI
