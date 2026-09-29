-- Prove2me | solution 1 for NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/92a76b4b-44a3-5fa1-896d-0688d35c9acc

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Theorems.Thm_Rep_nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq
import Theorems.Thm_Rep_finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime
import Theorems.Thm_NumberField_SUnits_finrank_groupCohomology_zero_sUnitsRep_add_one
import Theorems.Thm_NumberField_PlaceDecomp_card_over_fixedField_eq_card_orbitRel_quotient
import Theorems.Thm_NumberField_InfPlaceDecomp_card_infinitePlace_fixedField_eq_card_orbitRel_quotient
import Theorems.Thm_Rep_finrank_groupCohomology_zero_ofMulAction
import Theorems.Thm_NumberField_SUnits_sUnits_eq_unit
import Theorems.Thm_M4aHerbrand_finrank_sUnit_eq
import Theorems.Thm_NumberField_LevelArith_nonempty_repTorsionP_iso_repModP
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module IsDedekindDomain NumberField NumberField.LevelArith"
open scoped Classical NumberField.LevelArith

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace P2mS25DecompWD

open scoped TensorProduct Pointwise

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]

section Red

variable (p)
variable (V : Type*) [AddCommGroup V]

abbrev pSub : Submodule ℤ V := (p : ℤ) • ⊤

abbrev Red := V ⧸ pSub p V

lemma p_smul_mk (v : V) : (p : ℤ) • (Submodule.Quotient.mk v : Red p V) = 0 := by
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top

lemma p_nsmul_eq_zero (x : Red p V) : p • x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H v => rw [← natCast_zsmul]; exact p_smul_mk p V v

noncomputable scoped instance instModuleRed : Module (ZMod p) (Red p V) :=
  AddCommGroup.zmodModule (p_nsmul_eq_zero p V)

variable {V}
variable {W : Type*} [AddCommGroup W]

noncomputable def redMap (φ : V →ₗ[ℤ] W) : Red p V →ₗ[ZMod p] Red p W :=
  (Submodule.mapQ (pSub p V) (pSub p W) φ (by
      rintro _ ⟨v, -, rfl⟩
      show φ ((p : ℤ) • v) ∈ pSub p W
      rw [map_smul]
      exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top)).toAddMonoidHom.toZModLinearMap p

@[scoped simp] lemma redMap_mk (φ : V →ₗ[ℤ] W) (v : V) :
    redMap p φ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl

lemma redMap_id : redMap p (LinearMap.id : V →ₗ[ℤ] V) = LinearMap.id := by
  apply LinearMap.ext; intro x
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl

variable {U : Type*} [AddCommGroup U]

lemma redMap_comp (φ : V →ₗ[ℤ] W) (ψ : W →ₗ[ℤ] U) : redMap p (ψ ∘ₗ φ) = redMap p ψ ∘ₗ redMap p φ := by
  apply LinearMap.ext; intro x
  induction x using Submodule.Quotient.induction_on with
  | H v => rfl

variable (V)

noncomputable def redRep (ρ : Representation ℤ G V) : Representation (ZMod p) G (Red p V) where
  toFun g := redMap p (ρ g)
  map_one' := by rw [map_one]; exact redMap_id p
  map_mul' g h := by rw [map_mul]; exact redMap_comp p (ρ h) (ρ g)

@[scoped simp] lemma redRep_apply_mk (ρ : Representation ℤ G V) (g : G) (v : V) :
    redRep p V ρ g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (ρ g v) := rfl

end Red

section Functor

variable (p)
variable {V W U : Type*} [AddCommGroup V] [AddCommGroup W] [AddCommGroup U]

abbrev X (ρ : Representation ℤ G V) := (redRep p V ρ).asModule

noncomputable def redHom (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (φ : V →ₗ[ℤ] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) : X p ρ →ₗ[MonoidAlgebra (ZMod p) G] X p σ :=
  Representation.IntertwiningMap.equivLinearMapAsModule _ _
    ((redMap p φ).intertwiningMap_of_isIntertwiningMap (redRep p V ρ) (redRep p W σ) (fun g x => by
      induction x using Submodule.Quotient.induction_on with
      | H v => simp only [redRep_apply_mk, redMap_mk, hφ]))

@[scoped simp] lemma redHom_mk (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (φ : V →ₗ[ℤ] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) (v : V) :
    redHom p ρ σ φ hφ (Submodule.Quotient.mk v) = (Submodule.Quotient.mk (φ v) : Red p W) := rfl

lemma redHom_apply (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (φ : V →ₗ[ℤ] W)
    (hφ : ∀ g v, φ (ρ g v) = σ g (φ v)) (x : X p ρ) : redHom p ρ σ φ hφ x = redMap p φ x := rfl

noncomputable def redEquiv (ρ : Representation ℤ G V) (σ : Representation ℤ G W) (e : V ≃ₗ[ℤ] W)
    (he : ∀ g v, e (ρ g v) = σ g (e v)) : X p ρ ≃ₗ[MonoidAlgebra (ZMod p) G] X p σ :=
  LinearEquiv.ofLinear (redHom p ρ σ e.toLinearMap he)
    (redHom p σ ρ e.symm.toLinearMap (fun g w => by
      apply e.injective; rw [he]; simp))
    (by
      apply LinearMap.ext; intro x
      induction x using Submodule.Quotient.induction_on with
      | H v => simp [redHom_apply])
    (by
      apply LinearMap.ext; intro x
      induction x using Submodule.Quotient.induction_on with
      | H v => simp [redHom_apply])

end Functor

section Sublattice

variable (p)
variable {V : Type*} [AddCommGroup V] (ρ : Representation ℤ G V)

noncomputable def subRep (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : Representation ℤ G S where
  toFun g := (ρ g).restrict (fun v hv => hS g v hv)
  map_one' := by ext ⟨v, hv⟩; simp
  map_mul' g h := by ext ⟨v, hv⟩; simp

@[scoped simp] lemma subRep_apply_coe (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : G) (v : S) :
    ((subRep ρ S hS g v : S) : V) = ρ g v := rfl

noncomputable def incl (S T : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (hT : ∀ g, ∀ v ∈ T, ρ g v ∈ T)
    (hST : S ≤ T) : X p (subRep ρ S hS) →ₗ[MonoidAlgebra (ZMod p) G] X p (subRep ρ T hT) :=
  redHom p _ _ (Submodule.inclusion hST) (fun g v => rfl)

noncomputable def inclTop (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    X p (subRep ρ S hS) →ₗ[MonoidAlgebra (ZMod p) G] X p ρ :=
  redHom p _ _ S.subtype (fun g v => rfl)

def divP (S : Submodule ℤ V) : Submodule ℤ V := S.comap ((p : ℤ) • LinearMap.id)

lemma mem_divP {S : Submodule ℤ V} {v : V} : v ∈ divP p S ↔ (p : ℤ) • v ∈ S := Iff.rfl

lemma le_divP (S : Submodule ℤ V) : S ≤ divP p S := fun v hv => S.smul_mem _ hv

lemma divP_stable (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) : ∀ g, ∀ v ∈ divP p S, ρ g v ∈ divP p S := by
  intro g v hv
  rw [mem_divP] at hv ⊢
  rw [← map_smul]
  exact hS g _ hv

noncomputable def mulP (S : Submodule ℤ V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    X p (subRep ρ (divP p S) (divP_stable p ρ S hS)) →ₗ[MonoidAlgebra (ZMod p) G] X p (subRep ρ S hS) :=
  redHom p _ _ (((p : ℤ) • LinearMap.id : V →ₗ[ℤ] V).restrict (fun v hv => (mem_divP p).1 hv)) (fun g v => by
    apply Subtype.ext
    simp [LinearMap.restrict_apply, map_smul])

end Sublattice

section Tensor

variable (p)
variable (V : Type*) [AddCommGroup V]

noncomputable def toRed : V ⊗[ℤ] ZMod p →ₗ[ℤ] Red p V :=
  TensorProduct.lift
    { toFun := fun v => ((LinearMap.toSpanSingleton (ZMod p) (Red p V) (Submodule.Quotient.mk v)).toAddMonoidHom).toIntLinearMap
      map_add' := fun v w => by
        apply LinearMap.ext; intro a
        simp [LinearMap.toSpanSingleton_apply, Submodule.Quotient.mk_add, smul_add]
      map_smul' := fun n v => by
        apply LinearMap.ext; intro a
        show a • (Submodule.Quotient.mk (n • v) : Red p V) = n • (a • (Submodule.Quotient.mk v : Red p V))
        rw [Submodule.Quotient.mk_smul, smul_comm] }

@[scoped simp] lemma toRed_tmul (v : V) (a : ZMod p) : toRed p V (v ⊗ₜ a) = a • (Submodule.Quotient.mk v : Red p V) := by
  simp [toRed, LinearMap.toSpanSingleton_apply]

noncomputable def ofRed : Red p V →ₗ[ℤ] V ⊗[ℤ] ZMod p :=
  (pSub p V).liftQ ((TensorProduct.mk ℤ V (ZMod p)).flip 1) (by
    rintro _ ⟨v, -, rfl⟩
    show ((p : ℤ) • v) ⊗ₜ[ℤ] (1 : ZMod p) = 0
    rw [TensorProduct.smul_tmul]
    simp)

@[scoped simp] lemma ofRed_mk (v : V) : ofRed p V (Submodule.Quotient.mk v) = v ⊗ₜ (1 : ZMod p) := rfl

lemma toRed_ofRed (x : Red p V) : toRed p V (ofRed p V x) = x := by
  induction x using Submodule.Quotient.induction_on with
  | H v => simp

lemma ofRed_toRed (x : V ⊗[ℤ] ZMod p) : ofRed p V (toRed p V x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v a =>
    rw [toRed_tmul]
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective a
    rw [Int.cast_smul_eq_zsmul, ← Submodule.Quotient.mk_smul, ofRed_mk, TensorProduct.smul_tmul]
    congr 1
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Tensor

section Natural

variable (p)
variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

lemma toRed_natural (φ : V →ₗ[ℤ] W) (x : V ⊗[ℤ] ZMod p) :
    toRed p W (TensorProduct.map φ LinearMap.id x) = redMap p φ (toRed p V x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v a => simp [map_smul]
  | add x y hx hy => simp only [map_add, hx, hy]

variable (V)

noncomputable def tensorRedEquiv : V ⊗[ℤ] ZMod p ≃ₗ[ℤ] Red p V :=
  LinearEquiv.ofLinear (toRed p V) (ofRed p V) (LinearMap.ext (toRed_ofRed p V)) (LinearMap.ext (ofRed_toRed p V))

@[scoped simp] lemma tensorRedEquiv_apply (x : V ⊗[ℤ] ZMod p) : tensorRedEquiv p V x = toRed p V x := rfl

end Natural

end P2mS25DecompWD
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD"

namespace P2mS25MarksModP
open P2mS25DecompWD
open scoped TensorProduct Pointwise
variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
section ResIso

variable (p)
variable {V V' : Type} [AddCommGroup V] [AddCommGroup V'] (ρ : Representation ℤ G V) (ρ' : Representation ℤ G V')

theorem nonempty_iso_red_of_iso_tensor {H : Type} [Group H] (σ : Representation ℤ H V) (σ' : Representation ℤ H V')
    (i : Rep.of σ ⊗ Rep.trivial ℤ H (ZMod p) ≅ Rep.of σ' ⊗ Rep.trivial ℤ H (ZMod p)) :
    Nonempty (Rep.of (redRep p V σ) ≅ Rep.of (redRep p V' σ')) := by

  let EH : V ⊗[ℤ] ZMod p ≃ₗ[ℤ] V' ⊗[ℤ] ZMod p :=
    LinearEquiv.ofLinear i.hom.hom.toLinearMap i.inv.hom.toLinearMap
      (LinearMap.ext fun x => Rep.hom_inv_apply _ _ i x) (LinearMap.ext fun x => Rep.inv_hom_apply _ _ i x)
  have hEH : ∀ h x, EH (TensorProduct.map (σ h) LinearMap.id x) = TensorProduct.map (σ' h) LinearMap.id (EH x) :=
    fun h x => Rep.hom_comm_apply i.hom h x

  let E₀ : Red p V ≃ₗ[ℤ] Red p V' := (tensorRedEquiv p V).symm ≪≫ₗ EH ≪≫ₗ tensorRedEquiv p V'
  have hE₀ : ∀ h y, E₀ (redRep p V σ h y) = redRep p V' σ' h (E₀ y) := fun h y => by
    obtain ⟨x, rfl⟩ := (tensorRedEquiv p V).surjective y
    change toRed p V' (EH ((tensorRedEquiv p V).symm (redMap p (σ h) (tensorRedEquiv p V x)))) =
      redMap p (σ' h) (toRed p V' (EH ((tensorRedEquiv p V).symm (tensorRedEquiv p V x))))
    rw [tensorRedEquiv_apply, ← toRed_natural p (σ h) x, ← tensorRedEquiv_apply p V, LinearEquiv.symm_apply_apply,
      ← tensorRedEquiv_apply p V, LinearEquiv.symm_apply_apply, hEH, toRed_natural]

  let E₁ : Red p V ≃ₗ[ZMod p] Red p V' :=
    LinearEquiv.ofBijective ((E₀ : Red p V →+ Red p V').toZModLinearMap p) E₀.bijective
  refine ⟨Rep.mkIso (Representation.Equiv.mk E₁ (fun h => LinearMap.ext fun y => hE₀ h y))⟩

end ResIso
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD"

lemma finite_red (V : Type) [AddCommGroup V] [Module.Finite ℤ V] : Module.Finite (ZMod p) (Red p V) := by
  obtain ⟨s, hs⟩ := (inferInstance : Module.Finite ℤ V)
  refine ⟨⟨s.image (Submodule.Quotient.mk (p := pSub p V)), ?_⟩⟩
  rw [eq_top_iff]
  rintro x -
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    have hv : v ∈ Submodule.span ℤ (s : Set V) := by rw [hs]; exact Submodule.mem_top
    induction hv using Submodule.span_induction with
    | mem w hw =>
      exact Submodule.subset_span (by rw [Finset.coe_image]; exact ⟨w, hw, rfl⟩)
    | zero => rw [Submodule.Quotient.mk_zero]; exact Submodule.zero_mem _
    | add u w _ _ hu hw => rw [Submodule.Quotient.mk_add]; exact Submodule.add_mem _ hu hw
    | smul n w _ hw =>
      rw [Submodule.Quotient.mk_smul, ← Int.cast_smul_eq_zsmul (ZMod p) n]
      exact Submodule.smul_mem _ _ hw

end P2mS25MarksModP
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD"

namespace P2mS25HerbrandG

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
variable (p : ℕ) [Fact p.Prime] (S : Finset (HeightOneSpectrum (𝓞 E)))

local notation "G" => (K ≃ₐ[E] K)
local notation "U" => NumberField.SUnits.sUnitsRep E K S

abbrev VU : Type := ↥(NumberField.SUnits.sUnitsSubmodule E K S)

theorem finite_placesAbove : (NumberField.SUnits.placesAbove E K S).Finite := by
  have : NumberField.SUnits.placesAbove E K S ⊆ ⋃ v ∈ S, {w : HeightOneSpectrum (𝓞 K) | w.under (𝓞 E) = v} := by
    intro w hw
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    exact ⟨_, hw, rfl⟩
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun v _ => ?_) this

  have hfin := IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 K)
  refine Set.Finite.of_finite_image (f := fun w : HeightOneSpectrum (𝓞 K) => w.asIdeal) (hfin.subset ?_) ?_
  · rintro _ ⟨w, hw, rfl⟩
    refine ⟨w.isPrime, ⟨?_⟩⟩
    rw [Set.mem_setOf_eq] at hw
    rw [← hw]
    rfl
  · intro w _ w' _ h
    exact HeightOneSpectrum.ext h

noncomputable scoped instance : Finite ↥(NumberField.SUnits.placesAbove E K S) := (finite_placesAbove E K S).to_subtype

scoped instance moduleFinite_sUnits : Module.Finite ℤ (VU E K S) := by
  have h1 := (M4aHerbrand.finrank_sUnit_eq K (NumberField.SUnits.placesAbove E K S)).1

  let e : Additive ↥(Set.unit (NumberField.SUnits.placesAbove E K S) K) ≃+ VU E K S :=
    { toFun := fun x => ⟨Additive.ofMul ((Additive.toMul x : ↥(Set.unit (NumberField.SUnits.placesAbove E K S) K)) : Kˣ), by
        show Additive.toMul (Additive.ofMul _) ∈ NumberField.SUnits.sUnits E K S
        rw [NumberField.SUnits.sUnits_eq_unit]; exact (Additive.toMul x).2⟩
      invFun := fun x => Additive.ofMul ⟨Additive.toMul (x : Additive Kˣ), by
        have := x.2
        rw [NumberField.SUnits.mem_sUnitsSubmodule, NumberField.SUnits.sUnits_eq_unit] at this
        exact this⟩
      left_inv := fun x => rfl
      right_inv := fun x => rfl
      map_add' := fun x y => rfl }
  exact Module.Finite.equiv e.toIntLinearEquiv

end P2mS25HerbrandG
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

lemma shortExact_of {k : Type} [Field k] {A B C : Rep.{0} k G} (f : A ⟶ B) (g : B ⟶ C)
    (hinj : Function.Injective f.hom) (hsurj : Function.Surjective g.hom)
    (hrk : LinearMap.range f.hom.toLinearMap = LinearMap.ker g.hom.toLinearMap) :
    ∃ hfg : f ≫ g = 0, (CategoryTheory.ShortComplex.mk f g hfg).ShortExact := by
  have hfg : f ≫ g = 0 := by
    ext a
    have : f.hom a ∈ LinearMap.ker g.hom.toLinearMap := by rw [← hrk]; exact ⟨a, rfl⟩
    simpa using this
  refine ⟨hfg, ?_⟩
  haveI : Mono f := (Rep.mono_iff_injective f).2 hinj
  haveI : Epi g := (Rep.epi_iff_surjective g).2 hsurj
  have hex : (CategoryTheory.ShortComplex.mk f g hfg).Exact := by
    rw [← CategoryTheory.ShortComplex.exact_map_iff_of_faithful _ (forget₂ (Rep k G) (ModuleCat k)),
      CategoryTheory.ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact hrk
  exact CategoryTheory.ShortComplex.ShortExact.mk' hex inferInstance inferInstance

lemma finrank_invariants_tensor_congr {k : Type} [Field k] {A B : Rep.{0} k G} (i : A ≅ B) (M : Rep.{0} k G) :
    Module.finrank k (A ⊗ M : Rep.{0} k G).ρ.invariants = Module.finrank k (B ⊗ M : Rep.{0} k G).ρ.invariants := by
  let j : (A ⊗ M : Rep.{0} k G) ≅ B ⊗ M := MonoidalCategory.whiskerRightIso i M
  refine LinearEquiv.finrank_eq ?_
  refine LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (j.hom.hom.toLinearMap ∘ₗ (Submodule.subtype _)) fun x => ?_) ⟨?_, ?_⟩
  · intro g
    have := Rep.hom_comm_apply j.hom g (x : (A ⊗ M : Rep.{0} k G))
    rw [x.2 g] at this
    exact this.symm
  · intro x y hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    have h2 := congrArg j.inv.hom this
    change j.inv.hom (j.hom.hom x) = j.inv.hom (j.hom.hom y) at h2
    rwa [Rep.inv_hom_apply, Rep.inv_hom_apply] at h2
  · intro y
    refine ⟨⟨j.inv.hom y, fun g => ?_⟩, ?_⟩
    · have := Rep.hom_comm_apply j.inv g (y : (B ⊗ M : Rep.{0} k G))
      rw [y.2 g] at this
      exact this.symm
    · apply Subtype.ext
      exact Rep.hom_inv_apply _ _ j y

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] (ρ : Representation ℤ G V)

lemma torsion_stable : ∀ g, ∀ v ∈ Submodule.torsion ℤ V, ρ g v ∈ Submodule.torsion ℤ V := by
  rintro g v ⟨⟨a, ha⟩, hv⟩
  refine ⟨⟨a, ha⟩, ?_⟩
  change a • ρ g v = 0
  change a • v = 0 at hv
  rw [← map_smul, hv, map_zero]

noncomputable abbrev ρT : Representation ℤ G ↥(Submodule.torsion ℤ V) := subRep ρ _ (torsion_stable ρ)

abbrev Lam (V : Type) [AddCommGroup V] : Type := V ⧸ (Submodule.torsion ℤ V).toAddSubgroup

noncomputable def πL : V →ₗ[ℤ] Lam V := (QuotientAddGroup.mk' (Submodule.torsion ℤ V).toAddSubgroup).toIntLinearMap

@[scoped simp] lemma πL_apply (v : V) : πL v = (v : Lam V) := rfl

lemma πL_surjective : Function.Surjective (πL : V →ₗ[ℤ] Lam V) := QuotientAddGroup.mk_surjective

lemma πL_eq_zero_iff (v : V) : πL v = 0 ↔ v ∈ Submodule.torsion ℤ V := QuotientAddGroup.eq_zero_iff v

noncomputable def ρL : Representation ℤ G (Lam V) where
  toFun g := (QuotientAddGroup.map _ _ (ρ g).toAddMonoidHom (fun v hv => AddSubgroup.mem_comap.2 (torsion_stable ρ g v hv))).toIntLinearMap
  map_one' := by
    apply LinearMap.ext; intro x
    induction x using QuotientAddGroup.induction_on with
    | H v => simp
  map_mul' g h := by
    apply LinearMap.ext; intro x
    induction x using QuotientAddGroup.induction_on with
    | H v => simp

@[scoped simp] lemma ρL_apply_mk (g : G) (v : V) : ρL ρ g (v : Lam V) = (ρ g v : Lam V) := rfl

lemma πL_equivariant (g : G) (v : V) : πL (ρ g v) = ρL ρ g (πL v) := rfl

scoped instance lam_isTorsionFree : Module.IsTorsionFree ℤ (Lam V) := by
  rw [Submodule.isTorsionFree_iff_torsion_eq_bot, eq_bot_iff]
  rintro x ⟨⟨a, ha⟩, hx⟩
  induction x using QuotientAddGroup.induction_on with
  | H v =>
    change a • (v : Lam V) = 0 at hx
    rw [Submodule.mem_bot, ← πL_apply, πL_eq_zero_iff]
    rw [← πL_apply, ← map_smul, πL_eq_zero_iff] at hx
    obtain ⟨⟨b, hb⟩, hv⟩ := hx
    refine ⟨⟨b * a, mul_mem hb ha⟩, ?_⟩
    change (b * a) • v = 0
    rw [mul_smul]; exact hv

variable [Module.Finite ℤ V]

scoped instance lam_finite : Module.Finite ℤ (Lam V) := by
  haveI : AddGroup.FG V := Module.Finite.iff_addGroup_fg.1 inferInstance
  exact Module.Finite.iff_addGroup_fg.2 (QuotientAddGroup.fg _)

scoped instance lam_free : Module.Free ℤ (Lam V) := inferInstance

scoped instance tor_finite : Finite ↥(Submodule.torsion ℤ V) := by
  haveI : AddGroup.FG ↥(Submodule.torsion ℤ V) := Module.Finite.iff_addGroup_fg.1 inferInstance
  refine AddCommGroup.finite_of_fg_torsion _ fun x => ?_
  obtain ⟨⟨a, ha⟩, hx⟩ := x.2
  rw [isOfFinAddOrder_iff_zsmul_eq_zero]
  refine ⟨a, nonZeroDivisors.ne_zero ha, Subtype.ext ?_⟩
  exact hx

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)

variable (p)

noncomputable abbrev RT : Rep.{0} (ZMod p) G := Rep.of (redRep p _ (ρT ρ))

noncomputable abbrev RV : Rep.{0} (ZMod p) G := Rep.of (redRep p V ρ)

noncomputable abbrev RL : Rep.{0} (ZMod p) G := Rep.of (redRep p _ (ρL ρ))

noncomputable def fT : RT p ρ ⟶ RV p ρ :=
  Rep.ofHom ⟨redMap p (Submodule.torsion ℤ V).subtype, fun g => LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H v => rfl⟩

noncomputable def gL : RV p ρ ⟶ RL p ρ :=
  Rep.ofHom ⟨redMap p πL, fun g => LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H v => rfl⟩

lemma fT_hom_mk (t : Submodule.torsion ℤ V) :
    (fT p ρ).hom (Submodule.Quotient.mk t) = (Submodule.Quotient.mk (t : V) : Red p V) := rfl

lemma gL_hom_mk (v : V) :
    (gL p ρ).hom (Submodule.Quotient.mk v) = (Submodule.Quotient.mk (πL v) : Red p (Lam V)) := rfl

lemma fT_injective : Function.Injective (fT p ρ).hom := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H t =>
    rw [fT_hom_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
    obtain ⟨v, -, hv⟩ := hx

    have hvT : v ∈ Submodule.torsion ℤ V := by
      obtain ⟨⟨a, ha⟩, hta⟩ := t.2
      refine ⟨⟨a * p, mul_mem ha (mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero))⟩, ?_⟩
      change (a * (p : ℤ)) • v = 0
      rw [mul_smul, hv]; exact hta
    show (Submodule.Quotient.mk t : Red p (Submodule.torsion ℤ V)) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
    exact ⟨⟨v, hvT⟩, Submodule.mem_top, Subtype.ext hv⟩

lemma gL_surjective : Function.Surjective (gL p ρ).hom := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H l =>
    obtain ⟨v, rfl⟩ := πL_surjective l
    exact ⟨Submodule.Quotient.mk v, rfl⟩

lemma range_fT_eq_ker_gL :
    LinearMap.range (fT p ρ).hom.toLinearMap = LinearMap.ker (gL p ρ).hom.toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Submodule.Quotient.induction_on with
    | H t =>
      rw [LinearMap.mem_ker]
      change (gL p ρ).hom ((fT p ρ).hom (Submodule.Quotient.mk t)) = 0
      rw [fT_hom_mk, gL_hom_mk, (πL_eq_zero_iff (t : V)).2 t.2, Submodule.Quotient.mk_zero]
  · intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      rw [LinearMap.mem_ker] at hx
      change (gL p ρ).hom (Submodule.Quotient.mk v) = 0 at hx
      rw [gL_hom_mk, Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨l, -, hl⟩ := hx
      obtain ⟨w, rfl⟩ := πL_surjective l

      have hvw : v - (p : ℤ) • w ∈ Submodule.torsion ℤ V := by
        rw [← πL_eq_zero_iff, map_sub, map_smul, hl, sub_self]
      refine ⟨Submodule.Quotient.mk ⟨v - (p : ℤ) • w, hvw⟩, ?_⟩
      change (fT p ρ).hom (Submodule.Quotient.mk _) = Submodule.Quotient.mk v
      rw [fT_hom_mk, Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨-w, Submodule.mem_top, by simp⟩

theorem finrank_split (hG : (Nat.card G).Coprime p) (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (RV p ρ ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants =
      Module.finrank (ZMod p) (RT p ρ ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants +
      Module.finrank (ZMod p) (RL p ρ ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants := by
  obtain ⟨hfg, hX⟩ := shortExact_of (fT p ρ) (gL p ρ) (fT_injective p ρ) (gL_surjective p ρ) (range_fT_eq_ker_gL p ρ)
  haveI : FiniteDimensional (ZMod p) (RV p ρ) := finite_red V
  have hcop : (Nat.card (G ⧸ (⊥ : Subgroup G))).Coprime p := by
    rwa [Nat.card_congr (QuotientGroup.quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G).toEquiv]
  exact Rep.finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime (⊥ : Subgroup G) hcop _ hX
    (fun s hs => by rw [Subgroup.mem_bot] at hs; subst hs; exact map_one _) M

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)

noncomputable def mulCard : Lam V →ₗ[ℤ] V :=
  (QuotientAddGroup.lift (Submodule.torsion ℤ V).toAddSubgroup
    ((Nat.card ↥(Submodule.torsion ℤ V) : ℤ) • (AddMonoidHom.id V)) (fun t ht => by
      change ((Nat.card ↥(Submodule.torsion ℤ V) : ℤ)) • t = 0
      have := card_nsmul_eq_zero' (G := ↥(Submodule.torsion ℤ V)) (x := ⟨t, ht⟩)
      rw [natCast_zsmul]
      exact congrArg Subtype.val this)).toIntLinearMap

@[scoped simp] lemma mulCard_mk (v : V) : mulCard (v : Lam V) = (Nat.card ↥(Submodule.torsion ℤ V) : ℤ) • v := rfl

lemma mulCard_injective : Function.Injective (mulCard : Lam V →ₗ[ℤ] V) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  induction x using QuotientAddGroup.induction_on with
  | H v =>
    rw [mulCard_mk] at hx
    rw [← πL_apply, πL_eq_zero_iff]
    refine ⟨⟨(Nat.card ↥(Submodule.torsion ℤ V) : ℤ), mem_nonZeroDivisors_of_ne_zero ?_⟩, hx⟩
    exact_mod_cast (Nat.card_pos (α := ↥(Submodule.torsion ℤ V))).ne'

theorem finrank_invariants_lam_eq (H : Subgroup G) :
    Module.finrank ℤ (Representation.invariants ((ρL ρ).comp H.subtype)) = Module.finrank ℤ (Representation.invariants (ρ.comp H.subtype)) := by
  apply le_antisymm
  ·
    let μ : (Representation.invariants ((ρL ρ).comp H.subtype)) →ₗ[ℤ] (Representation.invariants (ρ.comp H.subtype)) :=
      LinearMap.codRestrict _ (mulCard ∘ₗ (Submodule.subtype _)) (fun l => by
        intro h
        obtain ⟨v, hv⟩ := πL_surjective (l : Lam V)
        have hl := l.2 h
        simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hl ⊢
        rw [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, ← hv, πL_apply, mulCard_mk, map_zsmul]

        have : (ρ (h : G) v : Lam V) = (v : Lam V) := by
          rw [← ρL_apply_mk, ← πL_apply v, hv]; exact hl
        rw [QuotientAddGroup.eq] at this
        have ht : -(ρ (h : G) v) + v ∈ Submodule.torsion ℤ V := this
        have := card_nsmul_eq_zero' (G := ↥(Submodule.torsion ℤ V)) (x := ⟨_, ht⟩)
        have h2 := congrArg Subtype.val this
        simp only [AddSubmonoidClass.coe_nsmul, ZeroMemClass.coe_zero, smul_add, smul_neg, neg_add_eq_zero] at h2
        rw [← natCast_zsmul, ← natCast_zsmul] at h2
        exact h2)
    have hμ : Function.Injective μ := by
      intro x y hxy
      apply Subtype.ext
      apply mulCard_injective
      have := congrArg Subtype.val hxy
      simpa [μ] using this
    exact LinearMap.finrank_le_finrank_of_injective hμ
  ·
    let φ : (Representation.invariants (ρ.comp H.subtype)) →ₗ[ℤ] (Representation.invariants ((ρL ρ).comp H.subtype)) :=
      LinearMap.codRestrict _ (πL ∘ₗ (Submodule.subtype _)) (fun v h => by
        have hv := v.2 h
        simp only [MonoidHom.coe_comp, Subgroup.coe_subtype, Function.comp_apply] at hv ⊢
        rw [LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype, ← πL_equivariant, hv])
    have hker : Module.IsTorsion ℤ (LinearMap.ker φ) := by
      rintro ⟨⟨v, hv⟩, hk⟩
      rw [LinearMap.mem_ker] at hk
      have hk' : πL v = 0 := congrArg Subtype.val hk
      rw [πL_eq_zero_iff] at hk'
      obtain ⟨a, ha⟩ := hk'
      exact ⟨a, Subtype.ext (Subtype.ext ha)⟩
    have h0 : Module.finrank ℤ (LinearMap.ker φ) = 0 := Module.finrank_eq_zero_iff_isTorsion.2 hker
    have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.ker φ)
    rw [h0, add_zero, LinearEquiv.finrank_eq φ.quotKerEquivRange] at h1
    rw [← h1]
    exact Submodule.finrank_mono le_top |>.trans (le_of_eq (finrank_top ℤ _))

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

section ProdTriv

variable {W : Type} [AddCommGroup W] (σ : Representation ℤ G W)

noncomputable def prodTriv : Representation ℤ G (W × ℤ) where
  toFun g := LinearMap.prodMap (σ g) LinearMap.id
  map_one' := by rw [map_one]; rfl
  map_mul' g h := by rw [map_mul]; rfl

@[scoped simp] lemma prodTriv_apply (g : G) (x : W × ℤ) : prodTriv σ g x = (σ g x.1, x.2) := rfl

noncomputable def invariantsProdTrivEquiv (H : Subgroup G) :
    Representation.invariants ((prodTriv σ).comp H.subtype) ≃+ Representation.invariants (σ.comp H.subtype) × ℤ where
  toFun x := (⟨x.1.1, fun h => congrArg Prod.fst (x.2 h)⟩, x.1.2)
  invFun y := ⟨(y.1.1, y.2), fun h => Prod.ext (y.1.2 h) rfl⟩
  left_inv x := rfl
  right_inv y := rfl
  map_add' x y := rfl

lemma isTorsionFree_submodule {M : Type} [AddCommGroup M] [Module.IsTorsionFree ℤ M] (N : Submodule ℤ M) :
    Module.IsTorsionFree ℤ N :=
  ⟨fun r hr x y hxy => Subtype.ext (hr.isSMulRegular (congrArg Subtype.val hxy : r • (x : M) = r • (y : M)))⟩

variable [Module.Finite ℤ W] [Module.IsTorsionFree ℤ W]

theorem finrank_H0_prodTriv (H : Subgroup G) :
    Module.finrank ℤ (groupCohomology (Rep.res H.subtype (Rep.of (prodTriv σ))) 0) =
      Module.finrank ℤ (Representation.invariants (σ.comp H.subtype)) + 1 := by
  haveI : Module.IsTorsionFree ℤ (Representation.invariants (σ.comp H.subtype)) := isTorsionFree_submodule _
  haveI : Module.Free ℤ (Representation.invariants (σ.comp H.subtype)) := inferInstance
  let e : groupCohomology (Rep.res H.subtype (Rep.of (prodTriv σ))) 0 ≃+ Representation.invariants (σ.comp H.subtype) × ℤ :=
    (groupCohomology.H0Iso (Rep.res H.subtype (Rep.of (prodTriv σ)))).toLinearEquiv.toAddEquiv.trans
      (invariantsProdTrivEquiv σ H)
  rw [LinearEquiv.finrank_eq e.toIntLinearEquiv, Module.finrank_prod, Module.finrank_self]

end ProdTriv
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

theorem finrank_H0_ofMulAction (X : Type) [MulAction G X] [Finite X] (H : Subgroup G) :
    Module.finrank ℤ (groupCohomology (Rep.res H.subtype (Rep.ofMulActionFinsupp ℤ G X)) 0) =
      Nat.card (MulAction.orbitRel.Quotient H X) :=
  Rep.finrank_groupCohomology_zero_ofMulAction (G := H) X

variable {V : Type} [AddCommGroup V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)

theorem nonempty_iso_red_prodTriv_ofMulAction (hG : (Nat.card G).Coprime p)
    (X : Type) [MulAction G X] [Finite X]
    (hmarks : ∀ H : Subgroup G, Module.finrank ℤ (Representation.invariants (ρ.comp H.subtype)) + 1 =
      Nat.card (MulAction.orbitRel.Quotient H X)) :
    Nonempty (Rep.of (redRep p _ (prodTriv (ρL ρ))) ≅ Rep.of (redRep p _ (Representation.ofMulActionFinsupp ℤ G X))) := by
  haveI : Module.Free ℤ (X →₀ ℤ) := inferInstance
  haveI : Module.Finite ℤ (X →₀ ℤ) := Module.Finite.finsupp
  obtain ⟨i⟩ := Rep.nonempty_tensor_trivial_zmod_iso_of_finrank_invariants_eq (p := p) hG
    (Rep.of (prodTriv (ρL ρ))) (Rep.ofMulActionFinsupp ℤ G X) (fun H => by
      rw [finrank_H0_prodTriv, finrank_H0_ofMulAction, finrank_invariants_lam_eq, hmarks])
  exact nonempty_iso_red_of_iso_tensor p (prodTriv (ρL ρ)) (Representation.ofMulActionFinsupp ℤ G X) i

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

noncomputable def invariantsEquivOfIso {k : Type} [Field k] {A B : Rep.{0} k G} (j : A ≅ B) :
    A.ρ.invariants ≃ₗ[k] B.ρ.invariants := by
  refine LinearEquiv.ofBijective
    (LinearMap.codRestrict _ (j.hom.hom.toLinearMap ∘ₗ (Submodule.subtype _)) fun x => ?_) ⟨?_, ?_⟩
  · intro g
    have := Rep.hom_comm_apply j.hom g (x : A)
    rw [x.2 g] at this
    exact this.symm
  · intro x y hxy
    apply Subtype.ext
    have := congrArg Subtype.val hxy
    simp only [LinearMap.codRestrict_apply, LinearMap.coe_comp, Function.comp_apply, Submodule.coe_subtype] at this
    have h2 := congrArg j.inv.hom this
    change j.inv.hom (j.hom.hom x) = j.inv.hom (j.hom.hom y) at h2
    rwa [Rep.inv_hom_apply, Rep.inv_hom_apply] at h2
  · intro y
    refine ⟨⟨j.inv.hom y, fun g => ?_⟩, ?_⟩
    · have := Rep.hom_comm_apply j.inv g (y : B)
      rw [y.2 g] at this
      exact this.symm
    · apply Subtype.ext
      exact Rep.hom_inv_apply _ _ j y

lemma finrank_invariants_congr {k : Type} [Field k] {A B : Rep.{0} k G} (j : A ≅ B) :
    Module.finrank k A.ρ.invariants = Module.finrank k B.ρ.invariants :=
  LinearEquiv.finrank_eq (invariantsEquivOfIso j)

section Unit
variable (p) (G)

theorem nonempty_iso_red_int_unit :
    Nonempty (Rep.of (redRep p ℤ (Representation.trivial ℤ G ℤ)) ≅ 𝟙_ (Rep.{0} (ZMod p) G)) := by

  let F0 : Red p ℤ →ₗ[ℤ] ZMod p := (pSub p ℤ).liftQ (Int.castAddHom (ZMod p)).toIntLinearMap (by
    rintro _ ⟨n, -, rfl⟩
    change ((((p : ℤ) • n : ℤ)) : ZMod p) = 0
    simp)
  let F : Red p ℤ →ₗ[ZMod p] ZMod p := (F0.toAddMonoidHom).toZModLinearMap p
  have hF : ∀ n : ℤ, F (Submodule.Quotient.mk n) = (n : ZMod p) := fun n => rfl
  let B : ZMod p →ₗ[ZMod p] Red p ℤ := LinearMap.toSpanSingleton _ _ (Submodule.Quotient.mk 1)
  have hFB : ∀ a, F (B a) = a := fun a => by
    change F (a • Submodule.Quotient.mk 1) = a
    rw [map_smul, hF, Int.cast_one, smul_eq_mul, mul_one]
  have hBF : ∀ x, B (F x) = x := fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H n =>
      rw [hF]
      change ((n : ZMod p)) • (Submodule.Quotient.mk 1 : Red p ℤ) = Submodule.Quotient.mk n
      rw [Int.cast_smul_eq_zsmul, ← Submodule.Quotient.mk_smul, smul_eq_mul, mul_one]
  let e : Red p ℤ ≃ₗ[ZMod p] ZMod p := LinearEquiv.ofLinear F B (LinearMap.ext hFB) (LinearMap.ext hBF)
  refine ⟨Rep.mkIso (Representation.Equiv.mk e (fun g => LinearMap.ext fun x => ?_))⟩
  induction x using Submodule.Quotient.induction_on with
  | H n => rfl

end Unit
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

section Perm
variable (p) (X : Type) [MulAction G X]

theorem nonempty_iso_red_finsupp_ofMulAction :
    Nonempty (Rep.of (redRep p (X →₀ ℤ) (Representation.ofMulActionFinsupp ℤ G X)) ≅ Rep.ofMulActionFinsupp (ZMod p) G X) := by
  let F0 : Red p (X →₀ ℤ) →ₗ[ℤ] (X →₀ ZMod p) :=
    (pSub p (X →₀ ℤ)).liftQ (Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod p))).toIntLinearMap (by
      rintro _ ⟨f, -, rfl⟩
      change Finsupp.mapRange.addMonoidHom (Int.castAddHom (ZMod p)) ((p : ℤ) • f) = 0
      rw [map_zsmul]
      ext x
      simp)
  let F : Red p (X →₀ ℤ) →ₗ[ZMod p] (X →₀ ZMod p) := (F0.toAddMonoidHom).toZModLinearMap p
  have hF : ∀ f : X →₀ ℤ, F (Submodule.Quotient.mk f) = Finsupp.mapRange (Int.cast : ℤ → ZMod p) (Int.cast_zero) f :=
    fun f => rfl
  let B : (X →₀ ZMod p) →ₗ[ZMod p] Red p (X →₀ ℤ) :=
    Finsupp.lift (Red p (X →₀ ℤ)) (ZMod p) X fun x => Submodule.Quotient.mk (Finsupp.single x 1)
  have hB : ∀ x a, B (Finsupp.single x a) = a • (Submodule.Quotient.mk (Finsupp.single x 1) : Red p (X →₀ ℤ)) :=
    fun x a => by simp [B, Finsupp.lift_apply]
  have hFB : F ∘ₗ B = LinearMap.id := by
    apply Finsupp.lhom_ext
    intro x a
    rw [LinearMap.comp_apply, hB, map_smul, hF, LinearMap.id_apply, Finsupp.mapRange_single, Int.cast_one,
      Finsupp.smul_single_one]
  have hBF : B ∘ₗ F = LinearMap.id := by
    apply LinearMap.ext
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H f =>
      rw [LinearMap.comp_apply, hF, LinearMap.id_apply]
      induction f using Finsupp.induction with
      | zero => simp
      | single_add x n f _ _ ih =>
        rw [Finsupp.mapRange_add (fun _ _ => Int.cast_add _ _), map_add, ih, Finsupp.mapRange_single, hB,
          Submodule.Quotient.mk_add, Int.cast_smul_eq_zsmul, ← Submodule.Quotient.mk_smul, Finsupp.smul_single_one]
  let e : Red p (X →₀ ℤ) ≃ₗ[ZMod p] (X →₀ ZMod p) := LinearEquiv.ofLinear F B hFB hBF
  refine ⟨Rep.mkIso (Representation.Equiv.mk e (fun g => ?_))⟩
  apply LinearMap.ext
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H f =>
    change F (redMap p (Representation.ofMulActionFinsupp ℤ G X g) (Submodule.Quotient.mk f)) =
      Representation.ofMulActionFinsupp (ZMod p) G X g (F (Submodule.Quotient.mk f))
    rw [redMap_mk, hF, hF]
    induction f using Finsupp.induction with
    | zero => simp
    | single_add x n f _ _ ih =>
      rw [map_add, Finsupp.mapRange_add (fun _ _ => Int.cast_add _ _),
        Finsupp.mapRange_add (fun _ _ => Int.cast_add _ _), map_add, ih,
        Representation.ofMulActionFinsupp_single, Finsupp.mapRange_single, Finsupp.mapRange_single,
        Representation.ofMulActionFinsupp_single]

end Perm
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
variable {V : Type} [AddCommGroup V] [Module.Finite ℤ V] (ρ : Representation ℤ G V)
variable (p)

section ProdSES
variable {W : Type} [AddCommGroup W] [Module.Finite ℤ W] [Module.IsTorsionFree ℤ W] (σ : Representation ℤ G W)

noncomputable abbrev RW : Rep.{0} (ZMod p) G := Rep.of (redRep p W σ)
noncomputable abbrev RWZ : Rep.{0} (ZMod p) G := Rep.of (redRep p _ (prodTriv σ))
noncomputable abbrev RZ : Rep.{0} (ZMod p) G := Rep.of (redRep p ℤ (Representation.trivial ℤ G ℤ))

noncomputable def fW : RW p σ ⟶ RWZ p σ :=
  Rep.ofHom ⟨redMap p (LinearMap.inl ℤ W ℤ), fun g => LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H w => change (Submodule.Quotient.mk _ : Red p (W × ℤ)) = Submodule.Quotient.mk _; simp⟩

noncomputable def gZ : RWZ p σ ⟶ RZ (G := G) p :=
  Rep.ofHom ⟨redMap p (LinearMap.snd ℤ W ℤ), fun g => LinearMap.ext fun x => by
    induction x using Submodule.Quotient.induction_on with
    | H w => rfl⟩

theorem finrank_prodTriv_split (hG : (Nat.card G).Coprime p) (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (RWZ p σ ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants =
      Module.finrank (ZMod p) (RW p σ ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants +
      Module.finrank (ZMod p) M.ρ.invariants := by
  have hinj : Function.Injective (fW p σ).hom := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    induction x using Submodule.Quotient.induction_on with
    | H w =>
      change (Submodule.Quotient.mk (w, (0 : ℤ)) : Red p (W × ℤ)) = 0 at hx
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
      obtain ⟨⟨w', n⟩, -, h⟩ := hx
      have h1 : (p : ℤ) • w' = w := congrArg Prod.fst h
      show (Submodule.Quotient.mk w : Red p W) = 0
      rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists]
      exact ⟨w', Submodule.mem_top, h1⟩
  have hsurj : Function.Surjective (gZ p σ).hom := by
    intro y
    induction y using Submodule.Quotient.induction_on with
    | H n => exact ⟨Submodule.Quotient.mk ((0 : W), n), rfl⟩
  have hrk : LinearMap.range (fW p σ).hom.toLinearMap = LinearMap.ker (gZ p σ).hom.toLinearMap := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      induction x using Submodule.Quotient.induction_on with
      | H w => rw [LinearMap.mem_ker]; rfl
    · intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H wn =>
        obtain ⟨w, n⟩ := wn
        rw [LinearMap.mem_ker] at hx
        change (Submodule.Quotient.mk n : Red p ℤ) = 0 at hx
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_smul_pointwise_iff_exists] at hx
        obtain ⟨m, -, hm⟩ := hx
        refine ⟨Submodule.Quotient.mk w, ?_⟩
        change (Submodule.Quotient.mk (w, (0 : ℤ)) : Red p (W × ℤ)) = Submodule.Quotient.mk (w, n)
        rw [Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
        refine ⟨((0 : W), -m), Submodule.mem_top, ?_⟩
        apply Prod.ext
        · simp
        · change (p : ℤ) • (-m) = 0 - n
          rw [smul_neg, zero_sub]
          exact congrArg Neg.neg hm
  obtain ⟨hfg, hX⟩ := shortExact_of (fW p σ) (gZ p σ) hinj hsurj hrk
  haveI : FiniteDimensional (ZMod p) (RWZ p σ) := finite_red (W × ℤ)
  have hcop : (Nat.card (G ⧸ (⊥ : Subgroup G))).Coprime p := by
    rwa [Nat.card_congr (QuotientGroup.quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G).toEquiv]
  have h1 := Rep.finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime (⊥ : Subgroup G) hcop _ hX
    (fun s hs => by rw [Subgroup.mem_bot] at hs; subst hs; exact map_one _) M

  obtain ⟨u⟩ := nonempty_iso_red_int_unit G p
  have h2 : Module.finrank (ZMod p) (RZ (G := G) p ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants =
      Module.finrank (ZMod p) M.ρ.invariants := by
    rw [finrank_invariants_tensor_congr u M, finrank_invariants_congr (λ_ M)]
  rw [← h2]
  exact h1

end ProdSES
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

theorem nonempty_iso_RT_torsionP (hG : (Nat.card G).Coprime p) :
    Nonempty (RT p ρ ≅ Rep.of (torsionP p ρ)) := by

  haveI : Finite (Rep.of (ρT ρ) : Rep.{0} ℤ G) := tor_finite
  obtain ⟨i⟩ := NumberField.LevelArith.nonempty_repTorsionP_iso_repModP p hG (Rep.of (ρT ρ))

  have e1 : RT p ρ ≅ repTorsionP p (Rep.of (ρT ρ)) := i.symm

  let f : ↥(Submodule.torsionBy ℤ ↥(Submodule.torsion ℤ V) (p : ℤ)) → ↥(Submodule.torsionBy ℤ V (p : ℤ)) :=
    fun x => ⟨(x : Submodule.torsion ℤ V), by
      have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact congrArg Subtype.val this⟩
  have hp0 : (p : ℤ) ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  let finv : ↥(Submodule.torsionBy ℤ V (p : ℤ)) → ↥(Submodule.torsionBy ℤ ↥(Submodule.torsion ℤ V) (p : ℤ)) :=
    fun v => ⟨⟨(v : V), ⟨⟨p, hp0⟩, (Submodule.mem_torsionBy_iff _ _).1 v.2⟩⟩, by
      rw [Submodule.mem_torsionBy_iff]; apply Subtype.ext; exact (Submodule.mem_torsionBy_iff _ _).1 v.2⟩
  let fadd : ↥(Submodule.torsionBy ℤ ↥(Submodule.torsion ℤ V) (p : ℤ)) →+ ↥(Submodule.torsionBy ℤ V (p : ℤ)) :=
    { toFun := f, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hbij : Function.Bijective fadd :=
    ⟨fun x y h => Subtype.ext (Subtype.ext (congrArg (fun z => ((z : ↥(Submodule.torsionBy ℤ V (p : ℤ))) : V)) h)),
     fun v => ⟨finv v, rfl⟩⟩
  let e : ↥(Submodule.torsionBy ℤ ↥(Submodule.torsion ℤ V) (p : ℤ)) ≃ₗ[ZMod p] ↥(Submodule.torsionBy ℤ V (p : ℤ)) :=
    LinearEquiv.ofBijective (fadd.toZModLinearMap p) hbij
  have e2 : repTorsionP p (Rep.of (ρT ρ)) ≅ Rep.of (torsionP p ρ) :=
    Rep.mkIso (Representation.Equiv.mk e (fun g => LinearMap.ext fun x => rfl))
  exact ⟨e1 ≪≫ e2⟩

theorem main (hG : (Nat.card G).Coprime p) (X : Type) [MulAction G X] [Finite X]
    (hmarks : ∀ H : Subgroup G, Module.finrank ℤ (Representation.invariants (ρ.comp H.subtype)) + 1 =
      Nat.card (MulAction.orbitRel.Quotient H X))
    (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (Rep.of (redRep p V ρ) ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants +
      Module.finrank (ZMod p) M.ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) G X ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants +
      Module.finrank (ZMod p) (Rep.of (torsionP p ρ) ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants := by
  have hsplit := finrank_split p ρ hG M
  obtain ⟨iT⟩ := nonempty_iso_RT_torsionP p ρ hG
  have hT := finrank_invariants_tensor_congr iT M
  have hprod := finrank_prodTriv_split p (ρL ρ) hG M
  obtain ⟨iL⟩ := nonempty_iso_red_prodTriv_ofMulAction (p := p) ρ hG X hmarks
  have hL := finrank_invariants_tensor_congr iL M
  obtain ⟨iX⟩ := nonempty_iso_red_finsupp_ofMulAction p (G := G) X
  have hX := finrank_invariants_tensor_congr iX M

  change Module.finrank (ZMod p) (RV p ρ ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants + _ = _
  rw [hsplit, hT, add_assoc, ← hprod, hL, hX, add_comm]

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace Generic

open P2mS25DecompWD P2mS25MarksModP
open scoped TensorProduct Pointwise

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

theorem natCard_orbitRel_quotient_sum (H : Type) [Group H] (α β : Type) [MulAction H α] [MulAction H β]
    [Finite α] [Finite β] :
    Nat.card (MulAction.orbitRel.Quotient H (α ⊕ β)) =
      Nat.card (MulAction.orbitRel.Quotient H α) + Nat.card (MulAction.orbitRel.Quotient H β) := by
  rw [← Nat.card_sum]
  apply Nat.card_congr

  let F : MulAction.orbitRel.Quotient H (α ⊕ β) → MulAction.orbitRel.Quotient H α ⊕ MulAction.orbitRel.Quotient H β :=
    Quotient.lift (Sum.elim (fun a => Sum.inl (Quotient.mk _ a)) (fun b => Sum.inr (Quotient.mk _ b))) (by
      rintro (a | b) (a' | b') ⟨h, hh⟩
      · change h • (Sum.inl a' : α ⊕ β) = Sum.inl a at hh
        simp only [Sum.elim_inl, Sum.inl.injEq]
        exact Quotient.sound ⟨h, Sum.inl_injective hh⟩
      · exact absurd hh (by simp [Sum.smul_def])
      · exact absurd hh (by simp [Sum.smul_def])
      · change h • (Sum.inr b' : α ⊕ β) = Sum.inr b at hh
        simp only [Sum.elim_inr, Sum.inr.injEq]
        exact Quotient.sound ⟨h, Sum.inr_injective hh⟩)
  let Finv : MulAction.orbitRel.Quotient H α ⊕ MulAction.orbitRel.Quotient H β → MulAction.orbitRel.Quotient H (α ⊕ β) :=
    Sum.elim (Quotient.lift (fun a => Quotient.mk _ (Sum.inl a)) (by
        rintro a a' ⟨h, hh⟩; exact Quotient.sound ⟨h, by change h • (Sum.inl a' : α ⊕ β) = _; rw [← hh]; rfl⟩))
      (Quotient.lift (fun b => Quotient.mk _ (Sum.inr b)) (by
        rintro b b' ⟨h, hh⟩; exact Quotient.sound ⟨h, by change h • (Sum.inr b' : α ⊕ β) = _; rw [← hh]; rfl⟩))
  refine ⟨F, Finv, fun x => ?_, fun y => ?_⟩
  · induction x using Quotient.inductionOn with
    | h s => rcases s with a | b <;> rfl
  · rcases y with qa | qb
    · induction qa using Quotient.inductionOn with | h a => rfl
    · induction qb using Quotient.inductionOn with | h b => rfl

section PermSum
variable (p) (α β : Type) [MulAction G α] [MulAction G β]

noncomputable def prodRep {A B : Type} [AddCommGroup A] [Module (ZMod p) A] [AddCommGroup B] [Module (ZMod p) B]
    (σ₁ : Representation (ZMod p) G A) (σ₂ : Representation (ZMod p) G B) : Representation (ZMod p) G (A × B) where
  toFun g := LinearMap.prodMap (σ₁ g) (σ₂ g)
  map_one' := by rw [map_one, map_one]; rfl
  map_mul' g h := by rw [map_mul, map_mul]; rfl

theorem finrank_perm_sum (hG : (Nat.card G).Coprime p) [Finite α] [Finite β]
    (M : Rep.{0} (ZMod p) G) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) G (α ⊕ β) ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) G α ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants +
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) G β ⊗ M : Rep.{0} (ZMod p) G).ρ.invariants := by
  let σ := prodRep p (Representation.ofMulActionFinsupp (ZMod p) G α) (Representation.ofMulActionFinsupp (ZMod p) G β)

  let e : (α ⊕ β →₀ ZMod p) ≃ₗ[ZMod p] (α →₀ ZMod p) × (β →₀ ZMod p) := Finsupp.sumFinsuppLEquivProdFinsupp (ZMod p)
  have he : ∀ g, e.toLinearMap ∘ₗ Representation.ofMulActionFinsupp (ZMod p) G (α ⊕ β) g = σ g ∘ₗ e.toLinearMap := fun g => by
    apply LinearMap.ext
    intro f
    apply Prod.ext
    · apply Finsupp.ext; intro a
      change (e (Representation.ofMulActionFinsupp (ZMod p) G (α ⊕ β) g f)).1 a =
        Representation.ofMulActionFinsupp (ZMod p) G α g (e f).1 a
      rw [Finsupp.fst_sumFinsuppLEquivProdFinsupp, Representation.ofMulActionFinsupp_apply, Representation.ofMulActionFinsupp_apply,
        Finsupp.fst_sumFinsuppLEquivProdFinsupp]
      rfl
    · apply Finsupp.ext; intro b
      change (e (Representation.ofMulActionFinsupp (ZMod p) G (α ⊕ β) g f)).2 b =
        Representation.ofMulActionFinsupp (ZMod p) G β g (e f).2 b
      rw [Finsupp.snd_sumFinsuppLEquivProdFinsupp, Representation.ofMulActionFinsupp_apply, Representation.ofMulActionFinsupp_apply,
        Finsupp.snd_sumFinsuppLEquivProdFinsupp]
      rfl
  let i : Rep.ofMulActionFinsupp (ZMod p) G (α ⊕ β) ≅ Rep.of σ := Rep.mkIso (Representation.Equiv.mk e he)
  rw [finrank_invariants_tensor_congr i M]

  let f : Rep.ofMulActionFinsupp (ZMod p) G α ⟶ Rep.of σ :=
    Rep.ofHom ⟨LinearMap.inl (ZMod p) _ _, fun g => LinearMap.ext fun x => Prod.ext rfl (by
      change (0 : β →₀ ZMod p) = Representation.ofMulActionFinsupp (ZMod p) G β g 0; rw [map_zero])⟩
  let g : Rep.of σ ⟶ Rep.ofMulActionFinsupp (ZMod p) G β :=
    Rep.ofHom ⟨LinearMap.snd (ZMod p) _ _, fun g => LinearMap.ext fun x => rfl⟩
  obtain ⟨hfg, hX⟩ := shortExact_of f g (fun x y h => (Prod.ext_iff.1 h).1) (fun y => ⟨((0 : α →₀ ZMod p), y), rfl⟩)
    (LinearMap.range_inl (ZMod p) _ _)
  haveI : FiniteDimensional (ZMod p) (Rep.of σ) :=
    (inferInstance : Module.Finite (ZMod p) ((α →₀ ZMod p) × (β →₀ ZMod p)))
  have hcop : (Nat.card (G ⧸ (⊥ : Subgroup G))).Coprime p := by
    rwa [Nat.card_congr (QuotientGroup.quotientBot : G ⧸ (⊥ : Subgroup G) ≃* G).toEquiv]
  exact Rep.finrank_invariants_tensor_eq_add_of_shortExact_of_trivial_of_coprime (⊥ : Subgroup G) hcop _ hX
    (fun s hs => by rw [Subgroup.mem_bot] at hs; subst hs; exact map_one _) M

end PermSum
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

end Generic
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

namespace P2mS25HerbrandG
open P2mS25DecompWD P2mS25MarksModP Generic
open scoped TensorProduct Pointwise

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]
variable (S : Finset (HeightOneSpectrum (𝓞 E)))

lemma finrank_H0_sUnits (H : Subgroup (K ≃ₐ[E] K)) :
    Module.finrank ℤ (groupCohomology (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S)) 0) =
      Module.finrank ℤ (Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype)) := by
  let e : groupCohomology (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S)) 0 ≃+
      Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype) :=
    (groupCohomology.H0Iso (Rep.res H.subtype (NumberField.SUnits.sUnitsRep E K S))).toLinearEquiv.toAddEquiv
  exact LinearEquiv.finrank_eq e.toIntLinearEquiv

end P2mS25HerbrandG
p2m_reactivate "P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25DecompWD P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.P2mS25HerbrandG P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add.Generic"

open P2mS25DecompWD P2mS25MarksModP Generic P2mS25HerbrandG in
theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    {p : ℕ} [Fact p.Prime] (hG : (Nat.card (K ≃ₐ[E] K)).Coprime p)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 E)))
    (M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)) [FiniteDimensional (ZMod p) M] :
    Module.finrank (ZMod p) (repModP p (NumberField.SUnits.sUnitsRep E K S) ⊗ M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) M.ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (K ≃ₐ[E] K)
          (Σ v : NumberField.InfinitePlace E, (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) ⊗ M :
          Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (K ≃ₐ[E] K)
          (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)) ⊗ M :
          Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants +
      Module.finrank (ZMod p) (repTorsionP p (NumberField.SUnits.sUnitsRep E K S) ⊗ M : Rep.{0} (ZMod p) (K ≃ₐ[E] K)).ρ.invariants := by

  haveI : Module.Finite E K := Module.Finite.of_restrictScalars_finite ℚ E K
  haveI : Finite (K ≃ₐ[E] K) := inferInstance
  haveI : Module.Finite ℤ (NumberField.SUnits.sUnitsRep E K S) := moduleFinite_sUnits E K S

  have hmarks : ∀ H : Subgroup (K ≃ₐ[E] K),
      Module.finrank ℤ (Representation.invariants ((NumberField.SUnits.sUnitsRep E K S).ρ.comp H.subtype)) + 1 =
        Nat.card (MulAction.orbitRel.Quotient H
          ((Σ v : NumberField.InfinitePlace E,
              (K ≃ₐ[E] K) ⧸ NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) ⊕
            (Σ v : S, (K ≃ₐ[E] K) ⧸ NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)))) := fun H => by
    rw [natCard_orbitRel_quotient_sum,
      ← NumberField.InfPlaceDecomp.card_infinitePlace_fixedField_eq_card_orbitRel_quotient E K H,
      ← NumberField.PlaceDecomp.card_over_fixedField_eq_card_orbitRel_quotient E K S H,
      ← finrank_H0_sUnits E K S H, NumberField.SUnits.finrank_groupCohomology_zero_sUnitsRep_add_one E K S H, add_comm]
  have hmain := Generic.main p (NumberField.SUnits.sUnitsRep E K S).ρ hG _ hmarks M
  rw [finrank_perm_sum p _ _ hG M] at hmain
  exact hmain

end S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add
end P2MW
export P2MW.S_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add (solution)
