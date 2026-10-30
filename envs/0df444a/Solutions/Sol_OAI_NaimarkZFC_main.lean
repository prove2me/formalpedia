-- Prove2me | solution 1 for OAI.NaimarkZFC.main
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T02:43:07.909639+00:00
-- url     : https://prove2.me/submissions/89572d92-d77e-42a2-9cfe-014cbbaa7be7

import Mathlib
import Definitions.Def_Naimark
import Definitions.Def_OAIQ115N028

section
-- module Solutions.OAIQ115_Naimark.Naimark_Dependencies
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_noMax _root_.OAI.NaimarkZFC.constructionIndex_orderBot _root_.OAI.NaimarkZFC.liftCStarAlgebra _root_.OAI.NaimarkZFC.liftStarRing _root_.OAI.NaimarkZFC.omittedAlgebra_cstar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology

open Filter Topology
open scoped CStarAlgebra ComplexOrder InnerProductSpace

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

section
variable {A B C : Type*} [CStarAlgebra A] [CStarAlgebra B] [CStarAlgebra C]

theorem StateExtensionUnique.of_comp {φ : A →⋆ₐ[ℂ] B} {ψ : B →⋆ₐ[ℂ] C}
    (hψ : Function.Injective ψ) {f : A →L[ℂ] ℂ}
    (hu : StateExtensionUnique (ψ.comp φ) f) : StateExtensionUnique φ f := by
  intro F G hF hG hrF hrG
  obtain ⟨F',hF',hrF'⟩ := exists_state_extension_of_injective ψ hψ F hF
  obtain ⟨G',hG',hrG'⟩ := exists_state_extension_of_injective ψ hψ G hG
  have hRF : restrictState (ψ.comp φ) F' = f := by
    rw [← restrictState_comp,hrF',hrF]
  have hRG : restrictState (ψ.comp φ) G' = f := by
    rw [← restrictState_comp,hrG',hrG]
  have he := hu F' G' hF' hG' hRF hRG
  rw [← hrF',← hrG',he]

variable [PartialOrder A] [StarOrderedRing A]
    [PartialOrder B] [StarOrderedRing B]

theorem pure_restrict_of_unique_factor
    (φ : A →⋆ₐ[ℂ] B) (ψ : B →⋆ₐ[ℂ] C) (hψ : Function.Injective ψ)
    (H : C →L[ℂ] ℂ) (hH : IsState H)
    (hp : IsPureState (restrictState (ψ.comp φ) H))
    (hu : StateExtensionUnique (ψ.comp φ) (restrictState (ψ.comp φ) H)) :
    IsPureState (restrictState ψ H) := by
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  have hb : IsState (restrictState ψ H) := isState_restrict ψ H hH
  have hr : restrictState φ (restrictState ψ H) = restrictState (ψ.comp φ) H :=
    restrictState_comp φ ψ H
  exact unique_lift_pure φ _ hp _ hb hr (fun g hg hgr =>
    hu.of_comp hψ g (restrictState ψ H) hg hb hgr hr)

end

section
variable {A : Type*} [CStarAlgebra A]

theorem pure_restrict_intermediate_subalgebra
    (S T : StarSubalgebra ℂ A) [IsClosed (S : Set A)] [IsClosed (T : Set A)]
    (hST : S ≤ T) (f : A →L[ℂ] ℂ) (hf : IsState f)
    (hp : IsPureState (restrictState S.subtype f))
    (hu : StateExtensionUnique S.subtype (restrictState S.subtype f)) :
    IsPureState (restrictState T.subtype f) := by
  let : PartialOrder S := CStarAlgebra.spectralOrder S
  let : StarOrderedRing S := CStarAlgebra.spectralOrderedRing S
  let : PartialOrder T := CStarAlgebra.spectralOrder T
  let : StarOrderedRing T := CStarAlgebra.spectralOrderedRing T
  let φ := StarSubalgebra.inclusion hST
  have he : T.subtype.comp φ = S.subtype := by ext a; rfl
  have hpi : IsPureState (restrictState (T.subtype.comp φ) f) := by rw [he]; exact hp
  have hui : StateExtensionUnique (T.subtype.comp φ)
      (restrictState (T.subtype.comp φ) f) := by rw [he]; exact hu
  exact pure_restrict_of_unique_factor φ T.subtype Subtype.val_injective f hf hpi hui

end

section

universe u
open Set Cardinal Ordinal

theorem countable_bounded_regular (c : Cardinal.{u}) (hc : c.IsRegular)
    (huc : ℵ₀ < c) (S : Set c.ord.ToType) (hS : S.Countable) :
    ∃ β : c.ord.ToType, ∀ x ∈ S, x < β := by
  let b : Ordinal.{u} := ⨆ x : S, (x.val : Ordinal) + 1
  have hb : b < c.ord := by
    apply Ordinal.iSup_add_one_lt_of_lt_cof
    · rw [hc.cof_ord]
      exact (Cardinal.le_aleph0_iff_set_countable.mpr hS).trans_lt huc
    · intro x
      exact x.val.toOrd.property
  refine ⟨Ordinal.ToType.mk ⟨b,hb⟩,?_⟩
  intro x hx
  apply Ordinal.ToType.mk.symm.lt_iff_lt.mp
  change x.toOrd.val < (Ordinal.ToType.mk ⟨b,hb⟩).toOrd.val
  simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using
    (Ordinal.lt_iSup_add_one (fun y : S => (y.val : Ordinal)) ⟨x,hx⟩)

theorem constructionCardinal_regular : constructionCardinal.{u}.IsRegular :=
  Cardinal.isRegular_succ Cardinal.aleph0_le_continuum

theorem countable_bounded_construction (S : Set constructionCardinal.{u}.ord.ToType)
    (hS : S.Countable) : ∃ β : constructionCardinal.{u}.ord.ToType,
      ∀ x ∈ S, x < β :=
  countable_bounded_regular constructionCardinal constructionCardinal_regular
    (Cardinal.aleph0_le_continuum.trans_lt (Order.lt_succ 𝔠)) S hS

theorem construction_initial_cardinal_le (β : constructionCardinal.{u}.ord.ToType) :
    (β : Ordinal).card ≤ 𝔠 := by
  have h : (β : Ordinal).card < constructionCardinal :=
    Cardinal.lt_ord.mp (show (β : Ordinal) < constructionCardinal.ord from β.toOrd.property)
  exact (Order.lt_succ_iff).mp h

end

section
universe u v w
variable {J : Type u} [Preorder J] {K : Type v}
    {A : Type w} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
    (D : J → Type w) [∀ j, CStarAlgebra (D j)]
    [∀ j, PartialOrder (D j)] [∀ j, StarOrderedRing (D j)]

theorem scheduled_pure_equivalent_to_reference
    (into : ∀ j, D j →⋆ₐ[ℂ] A) (hinj : ∀ j, Function.Injective (into j))
    (incl : ∀ {i j}, i ≤ j → D i →⋆ₐ[ℂ] D j)
    (hcomp : ∀ {i j} (h : i ≤ j), (into j).comp (incl h) = into i)
    (hu : ∀ j, PureUEP (into j))
    (f : A →L[ℂ] ℂ) (hf : IsPureState f)
    (hfp : ∀ j, IsPureState (restrictState (into j) f))
    (list : ∀ j, K → D j →L[ℂ] ℂ)
    (hlp : ∀ j η, IsPureState (list j η))
    (hex : ∀ j (g : D j →L[ℂ] ℂ), IsPureState g → ∃ η, list j η = g)
    (σ : J × K → J) (hσ : ∀ p, p.1 ≤ σ p)
    (next : J → J) (hn : ∀ j, j ≤ next j)
    (treated : ∀ j η, ∃ (G : D (next (σ (j,η))) →L[ℂ] ℂ)
      (hG : IsPureState G),
      restrictState (incl ((hσ (j,η)).trans (hn (σ (j,η))))) G = list j η ∧
      PureStateEquivalent G hG (restrictState (into (next (σ (j,η)))) f)
        (hfp (next (σ (j,η)))))
    (H : A →L[ℂ] ℂ) (hH : IsPureState H)
    (hearly : ∃ j, IsPureState (restrictState (into j) H)) :
    PureStateEquivalent H hH f hf := by
  obtain ⟨j,hj⟩ := hearly
  obtain ⟨η,hη⟩ := hex j _ hj
  obtain ⟨G,hG,hrG,heG⟩ := treated j η
  let k := next (σ (j,η))
  have hjk : j ≤ k := (hσ (j,η)).trans (hn (σ (j,η)))
  have hup : StateExtensionUnique ((into k).comp (incl hjk)) (list j η) := by
    rw [hcomp]
    exact hu j _ (hlp j η)
  have hsH : IsState (restrictState (into k) H) := isState_restrict (into k) H hH.1
  have hrH : restrictState (incl hjk) (restrictState (into k) H) = list j η := by
    rw [restrictState_comp,hcomp,hη]
  have hHG : restrictState (into k) H = G :=
    hup.of_comp (hinj k) _ _ hsH hG.1 hrH hrG
  exact pure_lifts_equivalent (into k) G (restrictState (into k) f) hG (hfp k)
    heG (hu k _ (hfp k)) H f hH hf hHG rfl

end

open scoped ComplexOrder CStarAlgebra
section
variable {B : Type*} [CStarAlgebra B]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_nontrivial_space (π : B →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hπ : IsIrreducible π) : Nontrivial H := by
  classical
  by_contra hn
  have : Subsingleton H := not_nontrivial_iff_subsingleton.mp hn
  apply hπ.1
  ext a x
  exact Subsingleton.elim _ _

end

open scoped ComplexOrder CStarAlgebra InnerProductSpace
section
universe u v w
variable {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {K : Type w} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

variable [PartialOrder A] [StarOrderedRing A]

theorem all_irreducibles_equivalent_of_pure_states
    (hall : ∀ (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      UnitarilyEquivalent (pureGNS f hf) (pureGNS g hg))
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (ρ : A →⋆ₙₐ[ℂ] (K →L[ℂ] K)) (hρ : IsIrreducible ρ) :
    UnitarilyEquivalent π ρ := by
  let := irreducible_nontrivial_space π hπ
  let := irreducible_nontrivial_space ρ hρ
  obtain ⟨ξ,hξ⟩ := exists_norm_eq H (show (0:ℝ) ≤ 1 by norm_num)
  obtain ⟨η,hη⟩ := exists_norm_eq K (show (0:ℝ) ≤ 1 by norm_num)
  obtain ⟨hf,hfπ⟩ := irreducible_vector_pure_equivalent π hπ ξ hξ
  obtain ⟨hg,hgρ⟩ := irreducible_vector_pure_equivalent ρ hρ η hη
  exact hfπ.symm.trans ((hall _ _ hf hg).trans hgρ)

end

open Filter Topology
open scoped CStarAlgebra

open Topology
open scoped CStarAlgebra ComplexOrder

open Filter Topology

open Filter Topology

section

universe u
open Set Cardinal Ordinal

theorem le_ordinalMajorant (f : Ordinal.{u} → Ordinal.{u}) (o : Ordinal.{u}) :
    f o ≤ ordinalMajorant f o := by
  rw [ordinalMajorant]
  exact le_max_left _ _

theorem ordinalMajorant_strictMono (f : Ordinal.{u} → Ordinal.{u}) :
    StrictMono (ordinalMajorant f) := by
  intro a b hab
  conv_rhs => rw [ordinalMajorant]
  apply lt_of_lt_of_le ?_ (le_max_right _ _)
  have h := Ordinal.lt_iSup_add_one
    (fun x : b.ToType => ordinalMajorant f (x : Ordinal)) (Ordinal.ToType.mk ⟨a,hab⟩)
  simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using h

theorem ordinalMajorant_lt (c : Cardinal.{u}) (hc : c.IsRegular)
    (f : Ordinal.{u} → Ordinal.{u}) (hf : ∀ o < c.ord, f o < c.ord)
    {o : Ordinal.{u}} (ho : o < c.ord) : ordinalMajorant f o < c.ord := by
  induction o using WellFoundedLT.induction with
  | ind o ih =>
    rw [ordinalMajorant]
    apply max_lt (hf o ho)
    apply Ordinal.iSup_add_one_lt_of_lt_cof
    · rw [Cardinal.mk_toType,hc.cof_ord]
      exact Cardinal.lt_ord.mp ho
    · intro x
      exact ih (x : Ordinal) x.toOrd.property (x.toOrd.property.trans ho)

theorem exists_injective_above (c : Cardinal.{u}) (hc : c.IsRegular)
    (f : c.ord.ToType → c.ord.ToType) :
    ∃ s : c.ord.ToType → c.ord.ToType, Function.Injective s ∧ ∀ x, f x ≤ s x := by
  classical
  let F (o : Ordinal.{u}) : Ordinal.{u} :=
    if h : o < c.ord then (f (Ordinal.ToType.mk ⟨o,h⟩) : Ordinal) else 0
  have hF (o : Ordinal.{u}) (ho : o < c.ord) : F o < c.ord := by
    simp only [F,dite_eq_left ho]
    exact (f (Ordinal.ToType.mk ⟨o,ho⟩)).toOrd.property
  let s (x : c.ord.ToType) : c.ord.ToType := Ordinal.ToType.mk
    ⟨ordinalMajorant F (x : Ordinal),ordinalMajorant_lt c hc F hF x.toOrd.property⟩
  refine ⟨s,?_,?_⟩
  · intro x y hxy
    have h := congrArg (fun z : c.ord.ToType => (z : Ordinal)) hxy
    have h' : ordinalMajorant F (x : Ordinal) = ordinalMajorant F (y : Ordinal) := by
      simpa only [s,Ordinal.ToType.toOrd,OrderIso.symm_apply_apply] using h
    have he := (ordinalMajorant_strictMono F).injective h'
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext he)
  · intro x
    apply Ordinal.ToType.mk.symm.le_iff_le.mp
    change (f x).toOrd.val ≤ (s x).toOrd.val
    simp only [s,Ordinal.ToType.toOrd,OrderIso.symm_apply_apply]
    have h := le_ordinalMajorant F (x : Ordinal)
    have hFx : F (x : Ordinal) = (f x : Ordinal) := by
      simp only [F, dite_eq_left (show (x : Ordinal) < c.ord from x.toOrd.property)]
      exact congrArg (fun z : c.ord.ToType => (f z : Ordinal))
        (OrderIso.apply_symm_apply Ordinal.ToType.mk x)
    rw [hFx] at h
    exact h

theorem exists_pair_schedule (c : Cardinal.{u}) (hc : c.IsRegular) :
    ∃ σ : c.ord.ToType × c.ord.ToType → c.ord.ToType,
      Function.Injective σ ∧ ∀ p, p.1 ≤ σ p := by
  have he : Cardinal.mk (c.ord.ToType × c.ord.ToType) = Cardinal.mk c.ord.ToType := by
    rw [Cardinal.mk_prod,Cardinal.mk_ord_toType,Cardinal.lift_id,Cardinal.mul_eq_self hc.aleph0_le]
  let e : (c.ord.ToType × c.ord.ToType) ≃ c.ord.ToType :=
    Classical.choice (Cardinal.eq.mp he)
  obtain ⟨s,hs,hbound⟩ := exists_injective_above c hc (fun x => (e.symm x).1)
  exact ⟨s ∘ e,hs.comp e.injective,fun p => by simpa using hbound (e p)⟩

end

open Filter Topology
open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open Filter Topology
open scoped InnerProductSpace

open Topology

open Topology

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Stages
attribute [-instance] _root_.OAI.NaimarkZFC.TracialStage.bond_directed _root_.OAI.NaimarkZFC.TracialStage.bond_isometric _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.liftCStarAlgebra _root_.OAI.NaimarkZFC.liftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section

attribute [instance] TracialStage.cstar TracialStage.order TracialStage.starOrder

namespace TracialStage

variable (X : TracialStage)

lemma infinite : ¬ FiniteDimensional ℂ X := by
  intro h
  exact carInfiniteDimensional (Module.Finite.of_injective X.base.toLinearMap X.base_injective)

end TracialStage
end

open scoped CStarAlgebra ComplexOrder

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace ComplexStarModule

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace CStarAlgebra

open scoped InnerProductSpace

open scoped InnerProductSpace

open scoped InnerProductSpace

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Omission
attribute [-instance] _root_.OAI.NaimarkZFC.constructionIndex_nonempty _root_.OAI.NaimarkZFC.liftCStarAlgebra _root_.OAI.NaimarkZFC.liftStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology
open scoped CStarAlgebra ComplexOrder

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

open Topology

section

universe u v
open Cardinal Topology TopologicalSpace

theorem countableSubsets_le_continuum (I : Type u) (hI : #I ≤ 𝔠) :
    #({s : Set I // s.Countable}) ≤ 𝔠 := by
  have h := Cardinal.mk_bounded_set_le I ℵ₀
  simp only [Cardinal.le_aleph0_iff_set_countable] at h
  exact h.trans ((Cardinal.power_le_power_right
    (max_le hI Cardinal.aleph0_le_continuum)).trans_eq Cardinal.continuum_power_aleph0)

theorem cardinal_of_countable_determination {A : Type v} (I P : Type u)
    (q : I → ℕ → A) (value : P → A → ℂ) (hI : #I ≤ 𝔠)
    (hdet : ∀ f : P, ∃ i : I, ∀ g : P,
      (∀ n, value f (q i n) = value g (q i n)) → f = g) : #P ≤ 𝔠 := by
  classical
  choose index hindex using hdet
  let code (f : P) : I × (ℕ → ℂ) := (index f,fun n => value f (q (index f) n))
  have hinj : Function.Injective code := by
    intro f g h
    have hi := congrArg Prod.fst h
    have hv := congrArg Prod.snd h
    apply hindex f g
    intro n
    have hh := congrFun hv n
    change value f (q (index f) n) = value g (q (index g) n) at hh
    change index f = index g at hi
    simpa only [← hi] using hh
  apply (Cardinal.mk_le_of_injective hinj).trans
  simp only [Cardinal.mk_prod,Cardinal.mk_arrow,Cardinal.mk_nat,Cardinal.mk_complex,
    Cardinal.lift_continuum,Cardinal.lift_id,
    Cardinal.continuum_power_aleph0]
  have hh : Cardinal.lift.{0,u} #I ≤ 𝔠 := by
    simpa only [Cardinal.lift_continuum] using (Cardinal.lift_le.mpr hI :
      Cardinal.lift.{0,u} #I ≤ Cardinal.lift.{0,u} 𝔠)
  exact (mul_le_mul' hh le_rfl).trans_eq Cardinal.continuum_mul_self

theorem continuous_eq_of_dense_values {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [T2Space Y] (q : ℕ → X) (hq : DenseRange q)
    (f g : X → Y) (hf : Continuous f) (hg : Continuous g)
    (h : ∀ n, f (q n) = g (q n)) : f = g :=
  hq.equalizer hf hg (funext h)

end

open Cardinal Topology TopologicalSpace
section
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

theorem generatedFamily_pureStates_le_continuum {J : Type}
    (base : Set A) (z : J → A) (hbase : IsSeparable base) (hJ : #J ≤ 𝔠)
    (hdet : ∀ (f : A →L[ℂ] ℂ), IsPureState f →
      ∃ S : Set J, S.Countable ∧
        StateExtensionUnique (generatedFamily base z S).subtype
          (restrictState (generatedFamily base z S).subtype f)) :
    #({f : A →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠 := by
  classical
  let C := {S : Set J // S.Countable}
  let B (S : C) := generatedFamily base z S.val
  let (S : C) : SeparableSpace (B S) :=
    (generatedFamily_separable base z hbase S.property).separableSpace
  let q (S : C) (n : ℕ) : A := (denseSeq (B S) n : A)
  apply cardinal_of_countable_determination C {f : A →L[ℂ] ℂ // IsPureState f}
    q (fun f a => f.val a) (countableSubsets_le_continuum J hJ)
  intro f
  obtain ⟨S,hS,hU⟩ := hdet f.val f.property
  refine ⟨⟨S,hS⟩,fun g hfg => ?_⟩
  have he : restrictState (B ⟨S,hS⟩).subtype f.val =
      restrictState (B ⟨S,hS⟩).subtype g.val := by
    apply DFunLike.ext'
    exact continuous_eq_of_dense_values (denseSeq (B ⟨S,hS⟩))
      (denseRange_denseSeq (B ⟨S,hS⟩))
      (restrictState (B ⟨S,hS⟩).subtype f.val) (restrictState (B ⟨S,hS⟩).subtype g.val)
      (restrictState (B ⟨S,hS⟩).subtype f.val).continuous
      (restrictState (B ⟨S,hS⟩).subtype g.val).continuous hfg
  apply Subtype.ext
  exact hU _ _ f.property.1 g.property.1 rfl he.symm

end

open Cardinal Topology TopologicalSpace
section
attribute [local instance] generatedFamily_isClosed
variable {A : Type} [CStarAlgebra A]

lemma subalgebra_uniqueRestriction_congr (S T : StarSubalgebra ℂ A)
    [IsClosed (S : Set A)] [IsClosed (T : Set A)] (hST : S = T)
    (f : A →L[ℂ] ℂ)
    (h : StateExtensionUnique S.subtype (restrictState S.subtype f)) :
    StateExtensionUnique T.subtype (restrictState T.subtype f) := by
  subst T
  exact h

namespace PeakingPairData
attribute [local instance] ambientSubalgebraOrder ambientSubalgebraStarOrder
variable [PartialOrder A] [StarOrderedRing A]
variable
    (base : Set A) (z : Ordinal.{0} → A) (Q : Ordinal.{0} → PeakingPairData A)
    (active : Set Ordinal.{0}) (I : Ordinal.{0} → Set Ordinal.{0}) (δ : Ordinal.{0})
    (hI : ∀ k < δ, I k ⊆ Set.Iio k)
    (hdata : ∀ k < δ, k ∈ active → ∀ i n, (Q k).peak i n ∈ generatedFamily base z (I k))
    (hpeak : ∀ k ∈ active, ∀ i n, (Q k).peak i n ∈ generatedFamily base z (Set.Iio k))
    (hchrono : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).AmbientPresentation (generatedFamily base z (Set.Iio k)) (hpeak k hk)
        (z k) (generatedFamily base z (Set.Iio (k+1))))
    (hinactive : ∀ k < δ, k ∉ active → z k = 1)
    (hne : ∀ k < δ, ∀ hk : k ∈ active,
      (Q k).PairDistinctOn (generatedFamily base z (Set.Iio k)) (hpeak k hk))
    (h0 : IsSimpleCStar (generatedFamily base z (Set.Iio 0)))
    (htrace : ∀ j < δ, ∀ k < δ, ∀ a, (Q j).trace a = (Q k).trace a)

include hI hdata hpeak hchrono hinactive hne h0 htrace in

theorem literal_pureStates_le_continuum
    (hIc : ∀ k < δ, (I k).Countable) (hbase : IsSeparable base)
    (hgen : generatedFamily base z (Set.Iio δ) = ⊤) (hδ : δ.card ≤ 𝔠) :
    #({f : A →L[ℂ] ℂ // IsPureState f}) ≤ 𝔠 := by
  let e : δ.ToType → Ordinal.{0} := fun k => (k : Ordinal.{0})
  have hei : Function.Injective e := by
    intro a b h
    exact Ordinal.ToType.mk.symm.injective (Subtype.ext h)
  have her : Set.range e = Set.Iio δ := by
    ext k
    constructor
    · rintro ⟨j,rfl⟩
      exact j.toOrd.property
    · intro hk
      exact ⟨Ordinal.ToType.mk ⟨k,hk⟩,by simp [e,Ordinal.ToType.toOrd]⟩
  apply generatedFamily_pureStates_le_continuum base (z ∘ e) hbase
    (by rwa [Cardinal.mk_toType])
  intro f hf
  obtain ⟨S,hSc,hS,_,_,_,_,hU⟩ := literal_countable_determination
    base z Q active I δ hI hdata hpeak hchrono hinactive hne h0 htrace hIc hbase hgen f hf
  refine ⟨e ⁻¹' S,hSc.preimage hei,?_⟩
  apply subalgebra_uniqueRestriction_congr (generatedFamily base z S) _ ?_ f hU
  rw [generatedFamily_reindex]
  have heS : e '' (e ⁻¹' S) = S := Set.image_preimage_eq_of_subset (her ▸ hS)
  rw [heS]

end PeakingPairData

end

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Recursion
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open Topology
section
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder

namespace ChronologicalData
variable {X : TracialStage} {δ : Ordinal.{0}} (D : ChronologicalData X δ)

include D in
lemma state_count (hδ : δ.card ≤ Cardinal.continuum) :
    Cardinal.mk {f : X →L[ℂ] ℂ // IsPureState f} ≤ Cardinal.continuum :=
  PeakingPairData.literal_pureStates_le_continuum (Set.range X.base) D.generator
    D.pair D.active D.dependency δ D.lower D.supported D.peak_mem D.chronological
    (fun k _ => D.inactive k) D.inequivalent (X.base_simple D.generator)
    (fun j _ k _ a => (D.trace j a).trans (D.trace k a).symm)
    D.countable X.base_separable D.generated hδ

end ChronologicalData
end

open Topology

open Topology

open Topology

open Topology

open Topology

open CategoryTheory

open CategoryTheory

open CategoryTheory Topology

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits
open CategoryTheory.SmallObject.SuccStruct

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J]

variable [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

variable (R : SuccessorRule J)

variable [WellFoundedLT J]

lemma recursivePrefixes_bot :
    (recursivePrefixes J R).val (op ⊥) =
      (Functor.const (Set.Iic (⊥ : J))).obj initial :=
  (recursionData J R).sectionsMk_val_op_bot _

lemma recursivePrefixes_succ (j : J) (hj : ¬ IsMax j) :
    (recursivePrefixes J R).val (op (Order.succ j)) =
      extendToSucc hj ((recursivePrefixes J R).val (op j))
        (R j hj ((recursivePrefixes J R).val (op j))).2 := by
  let e : (recursionData J R).Extension
      ((Functor.const (Set.Iic (⊥ : J))).obj initial) (Order.succ j) :=
    (Functor.WellOrderInductionData.Extension.instUnique (F := prefixSystem J)
      (d := recursionData J R) (val₀ := (Functor.const (Set.Iic (⊥ : J))).obj initial)
      (Order.succ j)).default
  have h := e.map_succ j (Order.lt_succ_of_not_isMax hj)
  change restrictionLE e.val le_rfl =
    extendToSucc hj (restrictionLE e.val (Order.le_succ j))
      (R j hj (restrictionLE e.val (Order.le_succ j))).2 at h
  have hr : restrictionLE e.val (Order.le_succ j) =
      (recursivePrefixes J R).val (op j) :=
    recursivePrefixes_compatible J R _ _ (Order.le_succ j)
  rw [hr] at h
  exact h

lemma recursiveTower_obj (j : J) :
    (recursiveTower J R).obj j = ((recursivePrefixes J R).val (op j)).obj ⟨j,le_rfl⟩ := rfl

lemma recursiveTower_arrow (i j : J) (hij : i ≤ j) :
    Arrow.mk ((recursiveTower J R).map (homOfLE hij)) =
      arrowMap ((recursivePrefixes J R).val (op j)) i j hij le_rfl :=
  gluePrefixes_arrow Set.univ (fun j => (recursivePrefixes J R).val (op j.val))
    (fun i j h => recursivePrefixes_compatible J R i j h) ⟨i,Set.mem_univ i⟩ ⟨j,Set.mem_univ j⟩ hij

lemma recursiveTower_bot : (recursiveTower J R).obj ⊥ = initial := by
  rw [recursiveTower_obj,recursivePrefixes_bot]
  rfl

lemma recursiveTower_succ_arrow (j : J) (hj : ¬ IsMax j) :
    Arrow.mk ((recursiveTower J R).map (homOfLE (Order.le_succ j))) =
      Arrow.mk (R j hj ((recursivePrefixes J R).val (op j))).2 := by
  rw [recursiveTower_arrow,recursivePrefixes_succ J R j hj]
  exact arrowSucc_extendToSucc hj _ _

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject
open CategoryTheory.Limits Opposite
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable (J : Type) [LinearOrder J] [SuccOrder J] [OrderBot J] [WellFoundedLT J]
  (R : SuccessorRule J)

lemma recursivePrefixes_limit (j : J) (hj : Order.IsSuccLimit j) :
    (recursivePrefixes J R).val (op j) =
      (recursionData J R).lift j hj (earlierPrefixes J R j) := by
  let e : (recursionData J R).Extension
      ((Functor.const (Set.Iic (⊥ : J))).obj initial) j :=
    (Functor.WellOrderInductionData.Extension.instUnique (F := prefixSystem J)
      (d := recursionData J R) (val₀ := (Functor.const (Set.Iic (⊥ : J))).obj initial)
      j).default
  have h := e.map_limit j hj le_rfl
  change e.val = (recursionData J R).lift j hj _ at h
  change e.val = _
  rw [h]
  congr 1
  ext k
  exact recursivePrefixes_compatible J R k.unop.val j k.unop.property.le

lemma recursiveTower_limit_height (j : J) (hj : Order.IsSuccLimit j) :
    ((recursiveTower J R).obj j).height =
      ⨆ i : Set.Iio j, ((recursiveTower J R).obj i.val).height := by
  let : Nonempty (Set.Iio j) := ⟨⟨⊥,hj.bot_lt⟩⟩
  rw [recursiveTower_obj,recursivePrefixes_limit J R j hj]
  change ((SuccStruct.ofCocone (directLimitCocone
    (gluePrefixes (Set.Iio j) (fun i => (recursivePrefixes J R).val (op i.val))
      (section_coherent J j (earlierPrefixes J R j))))).obj ⟨j,le_rfl⟩).height = _
  rw [SuccStruct.ofCocone_obj_eq_pt]
  rfl

lemma recursiveTower_succ_height
    (hr : ∀ j hj D, (R j hj D).1.height = (D.obj ⟨j,le_rfl⟩).height+1)
    (j : J) (hj : ¬ IsMax j) :
    ((recursiveTower J R).obj (Order.succ j)).height =
      ((recursiveTower J R).obj j).height+1 := by
  have h := congrArg (fun a : Arrow ChronologicalStage => a.right.height)
    (recursiveTower_succ_arrow J R j hj)
  exact h.trans (hr j hj ((recursivePrefixes J R).val (op j)))

theorem recursiveTower_height_le
    (hr : ∀ j hj D, (R j hj D).1.height = (D.obj ⟨j,le_rfl⟩).height+1)
    (o : J → Ordinal.{0}) (h0 : o ⊥ = 0)
    (hs : ∀ j, ¬ IsMax j → o j+1 ≤ o (Order.succ j))
    (hm : Monotone o) (j : J) :
    ((recursiveTower J R).obj j).height ≤ o j := by
  induction j using SuccOrder.limitRecOn with
  | isMin j hj =>
    obtain rfl : j = ⊥ := by simpa using hj
    rw [recursiveTower_bot,h0]
    exact le_rfl
  | succ j hj ih =>
    rw [recursiveTower_succ_height J R hr j hj]
    have hh : ((recursiveTower J R).obj j).height+1 ≤ o j+1 := by
      simpa using (Ordinal.add_le_add_iff_right 1).mpr ih
    exact hh.trans (hs j hj)
  | isSuccLimit j hj ih =>
    rw [recursiveTower_limit_height J R j hj]
    exact Ordinal.iSup_le fun i => (ih i.val i.property).trans (hm i.property.le)

end ChronologicalStage

open CategoryTheory Cardinal Classical
namespace TracialStage.Hom
variable {X Y : TracialStage} (j : Hom X Y) (f : X →L[ℂ] ℂ) (hf : IsPureState f)

lemma pureLift_restrict : restrictState j.map (j.pureLift f hf) = f :=
  ((j.uep f hf).exists_unique_pure j.injective hf).choose_spec.2.1
end TracialStage.Hom

namespace ChronologicalStage
variable (K : Type) (hK : 𝔠 ≤ #K) (X : ChronologicalStage)

lemma pureList_covers (hheight : X.height.card ≤ 𝔠)
    (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ k, pureList K hK X k = f := by
  classical
  have hc := X.history.state_count hheight
  simp only [pureList,dite_eq_left hc]
  exact (exists_pureState_list K hK hc X.stage.reference X.stage.reference_spec.1).choose_spec.2 f hf

variable {J : Type} [LinearOrder J]
  (σ : J × K → J) (hσ : ∀ p, p.1 ≤ σ p)
  (j : J) (D : Set.Iic j ⥤ ChronologicalStage)

lemma scheduledTarget_restrict (hi : Function.Injective σ)
    (p : J × K) (hp : σ p = j) :
    restrictState (D.map (homOfLE ((hσ p).trans_eq hp) :
      ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding.map
      (scheduledTarget K hK σ hσ j D) =
        pureList K hK (D.obj ⟨p.1,(hσ p).trans_eq hp⟩) p.2 := by
  classical
  have hx : ∃ q,σ q=j := ⟨p,hp⟩
  have he : hx.choose = p := hi (hx.choose_spec.trans hp.symm)
  subst p
  simp only [scheduledTarget,dite_eq_left hx]
  exact TracialStage.Hom.pureLift_restrict _ _ _

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]

omit orderBotJ in
lemma arrowMap_extendToSucc_through [OrderBot J] (j : J) (hj : ¬ IsMax j)
    (D : Set.Iic j ⥤ ChronologicalStage) {X : ChronologicalStage}
    (τ : D.obj ⟨j,le_rfl⟩ ⟶ X) (i : J) (hij : i ≤ j) :
    arrowMap (extendToSucc hj D τ) i (Order.succ j)
      (hij.trans (Order.le_succ j)) le_rfl =
      Arrow.mk ((D.map (homOfLE hij : ⟨i,hij⟩ ⟶ ⟨j,le_rfl⟩)) ≫ τ) := by
  apply Arrow.ext (extendToSucc_obj_eq hj D τ i hij)
    (extendToSucc_obj_succ_eq hj D τ)
  have hc := (extendToSucc hj D τ).map_comp
    (homOfLE hij : ⟨i,hij.trans (Order.le_succ j)⟩ ⟶ ⟨j,Order.le_succ j⟩)
    (homOfLE (Order.le_succ j) : (⟨j,Order.le_succ j⟩ : Set.Iic (Order.succ j)) ⟶ ⟨Order.succ j,le_rfl⟩)
  simp only [homOfLE_comp] at hc
  change (extendToSucc hj D τ).map
    (homOfLE (hij.trans (Order.le_succ j)) :
      ⟨i, hij.trans (Order.le_succ j)⟩ ⟶ ⟨Order.succ j, le_rfl⟩) = _
  rw [hc, extendToSucc_map hj D τ i j hij le_rfl,
    extendToSucc_map_le_succ, assoc, assoc, Iso.inv_hom_id_assoc]
  simp only [extendToSuccObjIso, extendToSucc.objIso,
    extendToSuccObjSuccIso, extendToSucc.objSuccIso,
    eqToIso.hom, eqToIso.inv, Arrow.mk_hom, assoc]
  rfl

variable (K : Type) (hK : 𝔠 ≤ #K)

variable (σ : J × K → J)
  (hσ : ∀ p,p.1 ≤ σ p)

variable [WellFoundedLT J]

lemma recursiveTower_through_succ_arrow (R : SuccessorRule J)
    (j : J) (hj : ¬ IsMax j) (i : J) (hij : i ≤ j) :
    Arrow.mk ((recursiveTower J R).map (homOfLE (hij.trans (Order.le_succ j)))) =
      Arrow.mk ((((recursivePrefixes J R).val (op j)).map
        (homOfLE hij : ⟨i,hij⟩ ⟶ ⟨j,le_rfl⟩)) ≫
          (R j hj ((recursivePrefixes J R).val (op j))).2) := by
  rw [recursiveTower_arrow,recursivePrefixes_succ J R j hj]
  exact arrowMap_extendToSucc_through j hj _ _ i hij

end ChronologicalStage

open Cardinal Ordinal

lemma constructionIndex_bot : ((⊥ : ConstructionIndex) : Ordinal) = 0 := by
  have h : (⊥ : ConstructionIndex) ≤ Ordinal.ToType.mk ⟨0,construction_ordinal_limit.bot_lt⟩ := bot_le
  have h' := Ordinal.ToType.mk.symm.monotone h
  change (↑(⊥ : ConstructionIndex) : Ordinal) ≤
    (Ordinal.ToType.mk ⟨0,construction_ordinal_limit.bot_lt⟩ : Ordinal) at h'
  simpa only [Ordinal.ToType.toOrd,OrderIso.symm_apply_apply,nonpos_iff_eq_zero] using h'

lemma constructionIndex_monotone : Monotone (fun j : ConstructionIndex => (j:Ordinal)) :=
  fun _ _ h => Ordinal.ToType.mk.symm.monotone h

lemma constructionIndex_succ_bound (j : ConstructionIndex) :
    (j:Ordinal)+1 ≤ ((Order.succ j : ConstructionIndex):Ordinal) := by
  apply Order.add_one_le_iff.mpr
  exact Ordinal.ToType.mk.symm.strictMono (Order.lt_succ j)

open CategoryTheory Topology
namespace ChronologicalStage
attribute [local instance] generatedFamily_isClosed
attribute [local instance] PeakingPairData.ambientSubalgebraOrder PeakingPairData.ambientSubalgebraStarOrder
variable (F : constructionCardinal.{0}.ord.ToType ⥤ ChronologicalStage)

lemma limit_countable_support_bounded (S : Set Ordinal.{0}) (hS : S.Countable)
    (hSl : S ⊆ Set.Iio (limitHeight F)) :
    ∃ j : constructionCardinal.{0}.ord.ToType, S ⊆ Set.Iio (F.obj j).height := by
  let e : S → constructionCardinal.{0}.ord.ToType :=
    fun k => limitIndex F k.val (hSl k.property)
  let : Countable S := hS.to_subtype
  obtain ⟨j,hj⟩ := countable_bounded_construction (Set.range e) (Set.countable_range e)
  refine ⟨j,?_⟩
  intro k hk
  have he := hj (e ⟨k,hk⟩) ⟨⟨k,hk⟩,rfl⟩
  exact (limitIndex_spec F k (hSl hk)).trans_le
    (F.map (homOfLE he.le)).height_le

lemma limit_support_le_range (S : Set Ordinal.{0})
    (j : constructionCardinal.{0}.ord.ToType) (hS : S ⊆ Set.Iio (F.obj j).height) :
    (limitHistory F).algebra S ≤ (limitEmbedding F j).map.range := by
  change generatedFamily (Set.range (limitStage F).base) (limitGenerator F) S ≤ _
  rw [← limit_generated_eq F j S hS]
  rw [← (F.obj j).history.image_generated_range (limitEmbedding F j)]
  exact generatedFamily_mono _ _ hS

theorem limit_eventual_pure (f : (limitStage F) →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ j : constructionCardinal.{0}.ord.ToType,
      IsPureState (restrictState (limitEmbedding F j).map f) := by
  obtain ⟨S,hSc,hS,_,_,_,hp,hu⟩ := (limitHistory F).countable_determination f hf
  obtain ⟨j,hSj⟩ := limit_countable_support_bounded F S hSc hS
  let φ := (limitEmbedding F j).map
  have hφ : Function.Injective φ := (limitEmbedding F j).injective
  let : IsClosed (φ.range : Set (limitStage F)) :=
    (NonUnitalStarAlgHom.isometry φ hφ).isClosedEmbedding.isClosed_range
  have hr := pure_restrict_intermediate_subalgebra
    ((limitHistory F).algebra S) φ.range (limit_support_le_range F S j hSj)
    f hf.1 hp hu
  let e : (F.obj j).stage ≃⋆ₐ[ℂ] φ.range :=
    StarAlgEquiv.ofBijective (φ.codRestrict φ.range (fun a => ⟨a,rfl⟩))
      ⟨fun a b h => hφ (congrArg Subtype.val h),by
        rintro ⟨a,⟨b,rfl⟩⟩; exact ⟨b,rfl⟩⟩
  exact ⟨j,isPureState_restrict_equiv e (restrictState φ.range.subtype f) hr⟩

end ChronologicalStage

open CategoryTheory Cardinal

universe u v w

theorem rankOne_isCompact {H : Type v} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (x y : H) :
    IsCompactOperator (InnerProductSpace.rankOne ℂ x y) := by
  rw [InnerProductSpace.rankOne_def']
  exact (isCompactOperator_of_locallyCompactSpace_rng
    (ContinuousLinearMap.toSpanSingleton ℂ x)).comp_clm (innerSL ℂ y)

theorem compacts_representation_map_one {A : Type u} [CStarAlgebra A]
    {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (φ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (hrange : ∀ T : H →L[ℂ] H, IsCompactOperator T → ∃ a : A, φ a = T) :
    φ 1 = ContinuousLinearMap.id ℂ H := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  · obtain ⟨a, ha⟩ := hrange _ (rankOne_isCompact x x)
    have hmul : φ 1 * InnerProductSpace.rankOne ℂ x x =
        InnerProductSpace.rankOne ℂ x x := by
      rw [← ha, ← map_mul, one_mul]
    have hv := congrArg (fun T : H →L[ℂ] H => T x) hmul
    simp only [mul_apply_eq_comp, InnerProductSpace.rankOne_apply,
      map_smul] at hv
    exact smul_right_injective H (inner_self_ne_zero.mpr hx) hv

theorem not_isIsomorphicToCompacts {A : Type u} [CStarAlgebra A]
    (hA : ¬ FiniteDimensional ℂ A)
    (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] :
    ¬ IsIsomorphicToCompacts A H := by
  rintro ⟨φ, hinj, hrange⟩
  have hone : φ 1 = ContinuousLinearMap.id ℂ H :=
    compacts_representation_map_one φ (fun T hT => (hrange T).mpr hT)
  have hcompact : IsCompactOperator (ContinuousLinearMap.id ℂ H) := by
    rw [← hone]
    exact (hrange (φ 1)).mp ⟨1, rfl⟩
  have : FiniteDimensional ℂ H :=
    FiniteDimensional.of_isCompactOperator_id (𝕜 := ℂ) hcompact
  let F : A →ₗ[ℂ] (H →L[ℂ] H) :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun c a => map_smul φ c a }
  exact hA (FiniteDimensional.of_injective F hinj)

lemma pureHomogeneity_of_equiv {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]
    [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    (e : A ≃⋆ₐ[ℂ] B)
    (h : ∀ (f g : A →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      PureStateEquivalent f hf g hg)
    (f g : B →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g) :
    PureStateEquivalent f hf g hg := by
  have hrf := isPureState_restrict_equiv e f hf
  have hrg := isPureState_restrict_equiv e g hg
  exact pure_lifts_equivalent e.toStarAlgHom _ _ hrf hrg (h _ _ hrf hrg)
    (StateExtensionUnique.of_surjective _ e.surjective _) f g hf hg rfl rfl

end NaimarkZFC

end

end OAI
end

section
-- module Solutions.OAIQ115_Naimark.Naimark_Tracial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace NaimarkZFC

open scoped CStarAlgebra ComplexOrder

open CategoryTheory Cardinal Classical
namespace ChronologicalStage
variable (X : ChronologicalStage)

lemma joiningChoice_height_unconditional (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    (joiningChoice_unconditional X f hf).1.height = X.height+1 :=
  (X.exists_joining_successor_unconditional f hf).choose_spec.choose_spec.1

lemma joiningChoice_treated_unconditional (f : X.stage →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ F : (joiningChoice_unconditional X f hf).1.stage →L[ℂ] ℂ, ∃ hF : IsPureState F,
      restrictState (joiningChoice_unconditional X f hf).2.embedding.map F = f ∧
      PureStateEquivalent (joiningChoice_unconditional X f hf).1.stage.reference
        (joiningChoice_unconditional X f hf).1.stage.reference_spec.1 F hF :=
  (X.exists_joining_successor_unconditional f hf).choose_spec.choose_spec.2

variable (K : Type) (hK : 𝔠 ≤ #K)
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]
  (σ : J × K → J) (hσ : ∀ p,p.1 ≤ σ p)

omit succOrderJ orderBotJ in
lemma scheduledRule_height_unconditional [SuccOrder J] [OrderBot J] (j : J) (hj : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage) :
    (scheduledRule_unconditional K hK σ hσ j hj D).1.height =
      (D.obj ⟨j,le_rfl⟩).height+1 :=
  joiningChoice_height_unconditional _ _ _

end ChronologicalStage

open CategoryTheory CategoryTheory.Category CategoryTheory.SmallObject Opposite Cardinal
open CategoryTheory.SmallObject.SuccStruct
namespace ChronologicalStage
variable {J : Type} [LinearOrder J] [succOrderJ : SuccOrder J] [orderBotJ : OrderBot J]
variable (K : Type) (hK : 𝔠 ≤ #K) (σ : J × K → J) (hσ : ∀ p,p.1 ≤ σ p)

omit succOrderJ orderBotJ in
lemma scheduledRule_treated_unconditional [SuccOrder J] [OrderBot J] (hi : Function.Injective σ) (j : J) (hj : ¬ IsMax j) (D : Set.Iic j ⥤ ChronologicalStage)
    (p : J × K) (hp : σ p = j) :
    Treated K hK p.2 (Arrow.mk
      ((D.map (homOfLE ((hσ p).trans_eq hp) :
        ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)) ≫
          (scheduledRule_unconditional K hK σ hσ j hj D).2)) := by
  obtain ⟨F,hF,hr,he⟩ := joiningChoice_treated_unconditional (D.obj ⟨j,le_rfl⟩)
    (scheduledTarget K hK σ hσ j D) (scheduledTarget_pure K hK σ hσ j D)
  refine ⟨F,hF,?_,he⟩
  change restrictState ((scheduledRule_unconditional K hK σ hσ j hj D).2.embedding.map.comp
    (D.map (homOfLE ((hσ p).trans_eq hp))).embedding.map) F = _
  exact (restrictState_comp _ _ F).symm.trans
    ((congrArg (restrictState (D.map (homOfLE ((hσ p).trans_eq hp) :
      ⟨p.1,(hσ p).trans_eq hp⟩ ⟶ ⟨j,le_rfl⟩)).embedding.map) hr).trans
      (scheduledTarget_restrict K hK σ hσ j D hi p hp))

variable [WellFoundedLT J]

theorem recursiveTower_treated_unconditional (hi : Function.Injective σ) (p : J × K) (hj : ¬ IsMax (σ p)) :
    Treated K hK p.2
      (Arrow.mk ((recursiveTower J (scheduledRule_unconditional K hK σ hσ)).map
        (homOfLE ((hσ p).trans (Order.le_succ (σ p)))))) := by
  rw [recursiveTower_through_succ_arrow (scheduledRule_unconditional K hK σ hσ) (σ p) hj p.1 (hσ p)]
  exact scheduledRule_treated_unconditional K hK σ hσ hi (σ p) hj _ p rfl

end ChronologicalStage

open CategoryTheory Cardinal
namespace ChronologicalStage

variable
    (σ : ConstructionIndex × ConstructionIndex → ConstructionIndex)
    (hσ : ∀ p,p.1 ≤ σ p)

lemma fullTower_height_unconditional (j : ConstructionIndex) :
    ((fullTower_unconditional σ hσ).obj j).height ≤ (j:Ordinal) :=
  recursiveTower_height_le _ _ (scheduledRule_height_unconditional _ _ _ _)
    (fun j => (j:Ordinal)) constructionIndex_bot
    (fun j _ => constructionIndex_succ_bound j) constructionIndex_monotone j

lemma fullTower_count_unconditional (j : ConstructionIndex) :
    ((fullTower_unconditional σ hσ).obj j).height.card ≤ 𝔠 :=
  (Ordinal.card_le_card (fullTower_height_unconditional σ hσ j)).trans (construction_initial_cardinal_le j)

theorem fullTower_pure_reference_unconditional (hi : Function.Injective σ)
    (f : limitStage (fullTower_unconditional σ hσ) →L[ℂ] ℂ) (hf : IsPureState f) :
    PureStateEquivalent f hf (limitStage (fullTower_unconditional σ hσ)).reference
      (limitStage (fullTower_unconditional σ hσ)).reference_spec.1 := by
  let F := fullTower_unconditional σ hσ
  let X := limitStage F
  let into := fun j => (limitEmbedding F j).map
  let incl := fun {i j : ConstructionIndex} (h : i ≤ j) => (F.map (homOfLE h)).embedding.map
  have hcomp : ∀ {i j} (h : i ≤ j), (into j).comp (incl h) = into i := by
    intro i j h
    ext a
    exact limit_embedding_compatible F i j h a
  have hfp : ∀ j, IsPureState (restrictState (into j) X.reference) := by
    intro j
    rw [(limitEmbedding F j).reference_map]
    exact (F.obj j).stage.reference_spec.1
  apply scheduled_pure_equivalent_to_reference (fun j => (F.obj j).stage)
    into (fun j => (limitEmbedding F j).injective) incl hcomp
    (fun j => (limitEmbedding F j).uep) X.reference X.reference_spec.1 hfp
    (fun j => pureList ConstructionIndex constructionIndex_cardinal (F.obj j))
    (fun j => pureList_pure ConstructionIndex constructionIndex_cardinal (F.obj j))
    (fun j g hg => pureList_covers ConstructionIndex constructionIndex_cardinal (F.obj j)
      (fullTower_count_unconditional σ hσ j) g hg)
    σ hσ Order.succ Order.le_succ ?_ f hf (limit_eventual_pure F f hf)
  intro j η
  obtain ⟨G,hG,hr,he⟩ := recursiveTower_treated_unconditional ConstructionIndex constructionIndex_cardinal
    σ hσ hi (j,η) (not_isMax _)
  refine ⟨G,hG,hr,?_⟩
  change PureStateEquivalent G hG
    (restrictState (limitEmbedding F _).map (limitStage F).reference) _
  simp only [TracialStage.Hom.reference_map]
  exact he.symm

end ChronologicalStage

universe u v w

theorem main_oai :
    ∃ (A : Type u) (_ : CStarAlgebra A),
      IsSimpleCStar A ∧ ¬ FiniteDimensional ℂ A ∧
      (∃ τ : A →L[ℂ] ℂ, IsFaithfulTracialState τ) ∧
      HasUniqueIrreducibleRepresentation.{u, v, w} A ∧
      ∀ (H : Type v) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
        ¬ IsIsomorphicToCompacts A H := by
  obtain ⟨σ,hi,hσ⟩ := exists_pair_schedule constructionCardinal.{0} constructionCardinal_regular
  let X := ChronologicalStage.limitStage (ChronologicalStage.fullTower_unconditional σ hσ)
  have hall : ∀ (f g : X →L[ℂ] ℂ) (hf : IsPureState f) (hg : IsPureState g),
      PureStateEquivalent f hf g hg := by
    intro f g hf hg
    exact (ChronologicalStage.fullTower_pure_reference_unconditional σ hσ hi f hf).trans
      (ChronologicalStage.fullTower_pure_reference_unconditional σ hσ hi g hg).symm
  let A := ULift.{u} X
  let e : X ≃⋆ₐ[ℂ] A := liftStarAlgEquiv X
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  have hinf : ¬ FiniteDimensional ℂ A := by
    intro h
    exact X.infinite (FiniteDimensional.of_injective e.toAlgEquiv.toLinearEquiv.toLinearMap e.injective)
  refine ⟨A,inferInstance,X.simple.of_equiv e,hinf,?_,?_,?_⟩
  · refine ⟨restrictState e.symm.toStarAlgHom X.trace,
      isState_restrict _ _ X.traceState,?_,?_⟩
    · intro a b
      change X.trace (e.symm (a*b)) = X.trace (e.symm (b*a))
      rw [map_mul e.symm a b, map_mul e.symm b a]
      exact X.tracial _ _
    · intro a ha
      change 0 < (X.trace (e.symm (star a*a))).re
      rw [map_mul e.symm (star a) a, map_star e.symm a]
      exact X.traceFaithful _ (fun h => ha (e.symm.injective (h.trans (map_zero e.symm).symm)))
  · intro H _ _ _ K _ _ _ π ρ hπ hρ
    exact all_irreducibles_equivalent_of_pure_states (pureHomogeneity_of_equiv e hall) π hπ ρ hρ
  · intro H _ _ _
    exact not_isIsomorphicToCompacts hinf H

end NaimarkZFC

end

end OAI
end

theorem solution.{u, v, w} : type_of% @OAI.NaimarkZFC.main_oai.{u, v, w} := @OAI.NaimarkZFC.main_oai.{u, v, w}
