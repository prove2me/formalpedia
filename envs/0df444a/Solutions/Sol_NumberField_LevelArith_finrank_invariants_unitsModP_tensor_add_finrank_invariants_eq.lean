-- Prove2me | solution 1 for NumberField.LevelArith.finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9be78872-ec1a-5196-b963-829600b941fe

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Theorems.Thm_NumberField_SUnits_finrank_invariants_repModP_sUnitsRep_tensor_add
import Theorems.Thm_NumberField_InfPlaceDecomp_exists_equiv_sigma_quotient_decomp_above
import Theorems.Thm_NumberField_PlaceTransport_exists_equiv_placesAbove_sigma_quotient_decomp_above
import Theorems.Thm_NumberField_LevelArith_nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar
import Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inl_equiv_infinitePlace
import Theorems.Thm_NumberField_LevelArith_exists_placesAbove_inr_embedding_heightOneSpectrum
import Theorems.Thm_NumberField_LevelArith_natCard_levelGal_eq_relIndex
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq
p2m_attr_erase "instance" "NumberField.LevelArith.instCommGroupUnitsModPow AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "NumberField.LevelArith.smul_mk NumberField.LevelArith.selmerRepInt_ρ_apply NumberField.LevelArith.selmerRepField_ρ_apply NumberField.LevelArith.unitsModPowMap_mk"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation IsDedekindDomain NumberField NumberField.LevelArith"
open scoped Classical NumberField.LevelArith NumberField.PlaceTransport NumberField Pointwise

namespace EqH

section EqFun
variable {k : Type} [CommRing k] {H : Type} [Group H] (Z : Type) [MulAction H Z] (N : Rep.{0} k H)

def eqFun : Submodule k (Z → N) where
  carrier := {F | ∀ (h : H) (z : Z), F (h • z) = N.ρ h (F z)}
  add_mem' {F G} hF hG := fun h z => by
    show F (h • z) + G (h • z) = N.ρ h (F z + G z)
    rw [hF h z, hG h z, map_add]
  zero_mem' := fun h z => by
    show (0 : N) = N.ρ h 0
    rw [map_zero]
  smul_mem' c F hF := fun h z => by
    show c • F (h • z) = N.ρ h (c • F z)
    rw [hF h z, map_smul]

variable {Z N}
lemma mem_eqFun (F : Z → N) : F ∈ eqFun Z N ↔ ∀ (h : H) (z : Z), F (h • z) = N.ρ h (F z) := Iff.rfl

end EqFun

section PermTensor
variable {k : Type} [CommRing k] {H : Type} [Group H] (Z : Type) [MulAction H Z] [Finite Z] (N : Rep.{0} k H)

noncomputable def E : ((Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H)) ≃ₗ[k] (Z → N) :=
  (TensorProduct.finsuppScalarLeft k N Z).trans (Finsupp.linearEquivFunOnFinite k N Z)

lemma E_tmul (f : Z →₀ k) (n : N) (z : Z) : E Z N (f ⊗ₜ[k] n) z = f z • n := by
  simp [E, TensorProduct.finsuppScalarLeft_apply_tmul_apply]

lemma E_ρ (h : H) (t : (Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H)) (z : Z) :
    E Z N ((Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H).ρ h t) z = N.ρ h (E Z N t (h⁻¹ • z)) := by
  induction t using TensorProduct.induction_on generalizing z with
  | zero => simp
  | tmul f n =>
    rw [Rep.tensor_ρ, Representation.tprod_apply, TensorProduct.map_tmul, E_tmul]
    change (Representation.ofMulActionFinsupp k H Z h f) z • N.ρ h n = N.ρ h (E Z N (f ⊗ₜ[k] n) (h⁻¹ • z))
    rw [E_tmul, map_smul, Representation.ofMulActionFinsupp_def, Finsupp.lmapDomain_apply]
    conv_lhs => rw [← smul_inv_smul h z, Finsupp.mapDomain_apply (MulAction.injective h)]
  | add x y hx hy =>
    rw [map_add, map_add, Pi.add_apply, hx, hy, ← map_add, map_add (E Z N) x y, Pi.add_apply]

noncomputable def invariantsEquivEqFun :
    (Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H).ρ.invariants ≃ₗ[k] eqFun Z N where
  toFun v := ⟨E Z N v.1, fun h z => by
    have hv := (Representation.mem_invariants _ _).1 v.2 h
    conv_lhs => rw [← hv]
    rw [E_ρ, inv_smul_smul]⟩
  invFun F := ⟨(E Z N).symm F.1, by
    rw [Representation.mem_invariants]
    intro h
    apply (E Z N).injective
    funext z
    rw [E_ρ, LinearEquiv.apply_symm_apply]
    have := F.2 h (h⁻¹ • z)
    rw [smul_inv_smul] at this
    exact this.symm⟩
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' c v := by apply Subtype.ext; exact map_smul _ _ _
  left_inv v := by apply Subtype.ext; exact (E Z N).symm_apply_apply _
  right_inv F := by apply Subtype.ext; exact (E Z N).apply_symm_apply _

lemma finrank_invariants_permTensor :
    Module.finrank k (Rep.ofMulActionFinsupp k H Z ⊗ N : Rep.{0} k H).ρ.invariants = Module.finrank k (eqFun Z N) :=
  LinearEquiv.finrank_eq (invariantsEquivEqFun Z N)

end PermTensor

section Transport
variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H] (φ : G →* H) (hφ : Function.Surjective φ)
  {Z : Type} [MulAction G Z] {Z' : Type} [MulAction H Z'] (e : Z ≃ Z') (he : ∀ (g : G) (z : Z), e (g • z) = φ g • e z)
  (M : Rep.{0} k H)

include hφ he in

noncomputable def eqFunTransport : eqFun Z (Rep.res φ M) ≃ₗ[k] eqFun Z' M where
  toFun F := ⟨fun z' => F.1 (e.symm z'), fun h z' => by
    obtain ⟨g, rfl⟩ := hφ h
    have : φ g • z' = e (g • e.symm z') := by rw [he, Equiv.apply_symm_apply]
    show F.1 (e.symm (φ g • z')) = M.ρ (φ g) (F.1 (e.symm z'))
    rw [this, Equiv.symm_apply_apply]
    exact F.2 g (e.symm z')⟩
  invFun F' := ⟨fun z => F'.1 (e z), fun g z => by
    show F'.1 (e (g • z)) = M.ρ (φ g) (F'.1 (e z))
    rw [he]
    exact F'.2 (φ g) (e z)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by apply Subtype.ext; funext z; show F.1 (e.symm (e z)) = F.1 z; rw [Equiv.symm_apply_apply]
  right_inv F' := by apply Subtype.ext; funext z'; show F'.1 (e (e.symm z')) = F'.1 z'; rw [Equiv.apply_symm_apply]

include hφ he in
lemma finrank_eqFun_transport :
    Module.finrank k (eqFun Z (Rep.res φ M)) = Module.finrank k (eqFun Z' M) :=
  LinearEquiv.finrank_eq (eqFunTransport φ hφ e he M)

end Transport

section TransportId
variable {k : Type} [CommRing k] {H : Type} [Group H]
  {Z : Type} [MulAction H Z] {Z' : Type} [MulAction H Z'] (e : Z ≃ Z') (he : ∀ (h : H) (z : Z), e (h • z) = h • e z)
  (M : Rep.{0} k H)

include he in
noncomputable def eqFunTransportId : eqFun Z M ≃ₗ[k] eqFun Z' M where
  toFun F := ⟨fun z' => F.1 (e.symm z'), fun h z' => by
    have : h • z' = e (h • e.symm z') := by rw [he, Equiv.apply_symm_apply]
    show F.1 (e.symm (h • z')) = M.ρ h (F.1 (e.symm z'))
    rw [this, Equiv.symm_apply_apply]
    exact F.2 h (e.symm z')⟩
  invFun F' := ⟨fun z => F'.1 (e z), fun g z => by
    show F'.1 (e (g • z)) = M.ρ g (F'.1 (e z))
    rw [he]
    exact F'.2 g (e z)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by apply Subtype.ext; funext z; show F.1 (e.symm (e z)) = F.1 z; rw [Equiv.symm_apply_apply]
  right_inv F' := by apply Subtype.ext; funext z'; show F'.1 (e (e.symm z')) = F'.1 z'; rw [Equiv.apply_symm_apply]

include he in
lemma finrank_eqFun_transportId : Module.finrank k (eqFun Z M) = Module.finrank k (eqFun Z' M) :=
  LinearEquiv.finrank_eq (eqFunTransportId e he M)

end TransportId

section FiniteEqFun
variable {k : Type} [Field k] {H : Type} [Group H] (Z : Type) [MulAction H Z] [Finite Z] (M : Rep.{0} k H)
  [FiniteDimensional k M]

scoped instance finite_eqFun : Module.Finite k (eqFun Z M) :=
  haveI : Module.Finite k (Z → M) := Module.Finite.pi
  Module.Finite.of_injective (eqFun Z M).subtype Subtype.val_injective

end FiniteEqFun

section SigmaSet
variable {k : Type} [CommRing k] {H : Type} [Group H] {ι : Type} [Fintype ι] (Z : ι → Type) [∀ i, MulAction H (Z i)]
  (N : Rep.{0} k H)

noncomputable def eqFunSigmaEquiv : eqFun (Σ i, Z i) N ≃ₗ[k] (∀ i, eqFun (Z i) N) where
  toFun F := fun i => ⟨fun z => F.1 ⟨i, z⟩, fun h z => F.2 h ⟨i, z⟩⟩
  invFun F := ⟨fun x => (F x.1).1 x.2, fun h x => (F x.1).2 h x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv F := by apply Subtype.ext; funext ⟨i, z⟩; rfl
  right_inv F := by funext i; rfl

end SigmaSet

section SigmaSetField
variable {k : Type} [Field k] {H : Type} [Group H] {ι : Type} [Fintype ι] (Z : ι → Type) [∀ i, MulAction H (Z i)]
  (N : Rep.{0} k H)

lemma finrank_eqFun_sigma [∀ i, Module.Finite k (eqFun (Z i) N)] :
    Module.finrank k (eqFun (Σ i, Z i) N) = ∑ i, Module.finrank k (eqFun (Z i) N) := by
  rw [LinearEquiv.finrank_eq (eqFunSigmaEquiv Z N), Module.finrank_pi_fintype]

end SigmaSetField

section ResSurj
variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H] (φ : G →* H) (hφ : Function.Surjective φ)

include hφ in
lemma invariants_res_eq (Y : Rep.{0} k H) : (Rep.res φ Y).ρ.invariants = Y.ρ.invariants := by
  ext v
  simp only [Representation.mem_invariants, MonoidHom.coe_comp, Function.comp_apply]
  constructor
  · intro h x; obtain ⟨g, rfl⟩ := hφ x; exact h g
  · intro h g; exact h (φ g)

include hφ in
lemma finrank_invariants_res_eq (Y : Rep.{0} k H) :
    Module.finrank k (Rep.res φ Y).ρ.invariants = Module.finrank k Y.ρ.invariants := by
  rw [invariants_res_eq φ hφ]

lemma invariants_res_tensor (T M : Rep.{0} k H) :
    (Rep.res φ T ⊗ Rep.res φ M : Rep.{0} k G).ρ.invariants = (Rep.res φ (T ⊗ M)).ρ.invariants := by
  ext v
  simp only [Representation.mem_invariants]
  exact Iff.rfl

end ResSurj

section Descent
variable {k : Type} [CommRing k] {G H : Type} [Group G] [Group H] (φ : G →* H) (hφ : Function.Surjective φ)
  (N : Rep.{0} k G) (hker : ∀ g : G, φ g = 1 → N.ρ g = 1)

include hker in
lemma rho_eq_of_apply_eq {g g' : G} (h : φ g = φ g') : N.ρ g = N.ρ g' := by
  have : g = g' * (g'⁻¹ * g) := by group
  rw [this, map_mul, hker (g'⁻¹ * g) (by rw [map_mul, map_inv, h, inv_mul_cancel]), mul_one]

noncomputable def descentρ : Representation k H N where
  toFun h := N.ρ (Function.surjInv hφ h)
  map_one' := hker _ (Function.surjInv_eq hφ 1)
  map_mul' a b := by
    rw [← map_mul]
    apply rho_eq_of_apply_eq φ N hker
    rw [map_mul, Function.surjInv_eq hφ, Function.surjInv_eq hφ, Function.surjInv_eq hφ]

noncomputable def descent : Rep.{0} k H := Rep.of (descentρ φ hφ N hker)

lemma descent_ρ_apply (g : G) : (descent φ hφ N hker).ρ (φ g) = N.ρ g :=
  rho_eq_of_apply_eq φ N hker (Function.surjInv_eq hφ (φ g))

noncomputable def isoResDescent : N ≅ Rep.res φ (descent φ hφ N hker) :=
  Rep.mkIso (Representation.Equiv.mk (LinearEquiv.refl k N) fun g => by
    apply LinearMap.ext; intro v
    show N.ρ g v = (descent φ hφ N hker).ρ (φ g) v
    exact congrFun (congrArg DFunLike.coe (descent_ρ_apply φ hφ N hker g).symm) v)

end Descent

end EqH
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH"

set_option linter.unusedSectionVars false

namespace EqH

section Subset
variable {G X : Type} [Group G] [MulAction G X]

@[reducible] def subsetMulAction (P : Set X) (hP : ∀ (g : G) (x : X), x ∈ P → g • x ∈ P) : MulAction G ↥P where
  smul g x := ⟨g • x.1, hP g x.1 x.2⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

end Subset
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH"

section FinitePlaces
variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

abbrev W (q : ℕ) : Set (HeightOneSpectrum (𝓞 K)) := {w | ((q : 𝓞 K)) ∈ w.asIdeal}

lemma smul_natCast_ringOfIntegers (σ : K ≃ₐ[E] K) (q : ℕ) : σ • ((q : 𝓞 K)) = (q : 𝓞 K) := by
  rw [← MulSemiringAction.toRingHom_apply, map_natCast]

lemma W_stable (q : ℕ) : ∀ (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)), w ∈ W K q → σ • w ∈ W K q := by
  intro σ w hw
  show ((q : 𝓞 K)) ∈ (σ • w).asIdeal
  rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, smul_natCast_ringOfIntegers]
  exact hw

noncomputable scoped instance mulActionW (q : ℕ) : MulAction (K ≃ₐ[E] K) ↥(W K q) := subsetMulAction (W K q) (W_stable E K q)

lemma coe_smul_W (q : ℕ) (σ : K ≃ₐ[E] K) (w : ↥(W K q)) : ((σ • w : ↥(W K q)) : HeightOneSpectrum (𝓞 K)) = σ • (w : HeightOneSpectrum (𝓞 K)) := rfl

theorem finite_W {q : ℕ} (hq : q ≠ 0) : Finite ↥(W K q) := by
  have hI : (Ideal.span {((q : 𝓞 K))} : Ideal (𝓞 K)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hq
  have := Ideal.finite_factors hI
  refine Set.Finite.to_subtype (this.subset fun w hw => ?_)
  show w.asIdeal ∣ Ideal.span {((q : 𝓞 K))}
  rw [Ideal.dvd_span_singleton]
  exact hw

lemma under_smul (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)) : (σ • w).under (𝓞 E) = w.under (𝓞 E) := by
  apply HeightOneSpectrum.ext
  rw [HeightOneSpectrum.under_asIdeal, HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • (algebraMap (𝓞 E) (𝓞 K) x) = algebraMap (𝓞 E) (𝓞 K) x := by
    apply Subtype.ext
    show σ⁻¹ (algebraMap E K (x : E)) = algebraMap E K (x : E)
    exact AlgEquiv.commutes _ _
  rw [this]

lemma placesAbove_stable (S : Finset (HeightOneSpectrum (𝓞 E))) :
    ∀ (σ : K ≃ₐ[E] K) (w : HeightOneSpectrum (𝓞 K)), w ∈ NumberField.SUnits.placesAbove E K S →
      σ • w ∈ NumberField.SUnits.placesAbove E K S := by
  intro σ w hw
  rw [NumberField.SUnits.mem_placesAbove] at hw ⊢
  rw [under_smul]; exact hw

noncomputable scoped instance mulActionPlacesAbove (S : Finset (HeightOneSpectrum (𝓞 E))) :
    MulAction (K ≃ₐ[E] K) ↥(NumberField.SUnits.placesAbove E K S) :=
  subsetMulAction _ (placesAbove_stable E K S)

lemma coe_smul_placesAbove (S : Finset (HeightOneSpectrum (𝓞 E))) (σ : K ≃ₐ[E] K) (w : ↥(NumberField.SUnits.placesAbove E K S)) :
    ((σ • w : ↥(NumberField.SUnits.placesAbove E K S)) : HeightOneSpectrum (𝓞 K)) = σ • (w : HeightOneSpectrum (𝓞 K)) := rfl

end FinitePlaces
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH"

end EqH
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH"

namespace TateK

noncomputable def invariantsEquiv {k : Type} [CommRing k] {G : Type} [Group G] {A B : Rep.{0} k G} (e : A ≅ B) :
    A.ρ.invariants ≃ₗ[k] B.ρ.invariants where
  toFun v := ⟨e.hom.hom v.1, fun g => by rw [← Rep.hom_comm_apply, v.2 g]⟩
  invFun w := ⟨e.inv.hom w.1, fun g => by rw [← Rep.hom_comm_apply, w.2 g]⟩
  map_add' v w := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a v := by apply Subtype.ext; exact map_smul _ _ _
  left_inv v := by apply Subtype.ext; simp
  right_inv w := by apply Subtype.ext; simp

lemma finrank_invariants_eq_of_iso {k : Type} [CommRing k] {G : Type} [Group G] {A B : Rep.{0} k G} (e : A ≅ B) :
    Module.finrank k A.ρ.invariants = Module.finrank k B.ρ.invariants :=
  LinearEquiv.finrank_eq (invariantsEquiv e)
end TateK
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH"

local instance EqHP.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
local instance EqHP.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
local instance EqHP.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
scoped instance EqHP.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) := IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)

p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqHP"
namespace EqHP

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
  [Normal ↥K ↥(levelField K L hKL)]

scoped instance isGaloisK : IsGalois ↥K Qbar := IsGalois.tower_top_intermediateField K

scoped instance isGaloisLevel : IsGalois ↥K ↥(levelField K L hKL) := by
  haveI : Algebra.IsSeparable ↥K ↥(levelField K L hKL) := inferInstance
  exact ⟨⟩

lemma levelGal_surjective : Function.Surjective (levelGal K L hKL) := by
  intro σ
  obtain ⟨τ, hτ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(levelField K L hKL)) Qbar σ
  refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm τ, ?_⟩
  show (AlgEquiv.restrictNormalHom ↥(levelField K L hKL)) ((IntermediateField.fixingSubgroupEquiv K) ((IntermediateField.fixingSubgroupEquiv K).symm τ)) = σ
  rw [MulEquiv.apply_symm_apply, hτ]

lemma mem_fixing_of_levelGal_eq_one (γ : ↥K.fixingSubgroup) (hγ : levelGal K L hKL γ = 1) :
    (γ : Γ) ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have := levelGal_apply_coe K L hKL γ ⟨x, (IntermediateField.mem_extendScalars hKL).2 hx⟩
  rw [hγ] at this
  exact this.symm

section Assembly
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hnorm : IsNormalLevel K L)
  (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
  (htriv : ∀ s : ↥K.fixingSubgroup, (s : Γ) ∈ L.fixingSubgroup → N.ρ s = 1)

include htriv in
lemma hker : ∀ γ : ↥K.fixingSubgroup, levelGal K L hKL γ = 1 → N.ρ γ = 1 :=
  fun γ h => htriv γ (mem_fixing_of_levelGal_eq_one K L hKL γ h)

noncomputable def M : Rep.{0} (ZMod p) (LevelGal K L hKL) :=
  EqH.descent (levelGal K L hKL) (levelGal_surjective K L hKL) N (hker K L hKL N htriv)

noncomputable def eN : N ≅ Rep.res (levelGal K L hKL) (M K L hKL N htriv) :=
  EqH.isoResDescent (levelGal K L hKL) (levelGal_surjective K L hKL) N (hker K L hKL N htriv)

scoped instance finiteM : FiniteDimensional (ZMod p) (M K L hKL N htriv) := inferInstanceAs (FiniteDimensional (ZMod p) N)

lemma term_infl (T : Rep.{0} (ZMod p) (LevelGal K L hKL)) :
    Module.finrank (ZMod p) (inflLevel K L hKL T ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      Module.finrank (ZMod p) (T ⊗ M K L hKL N htriv : Rep.{0} (ZMod p) (LevelGal K L hKL)).ρ.invariants := by
  rw [TateK.finrank_invariants_eq_of_iso (whiskerLeftIso (inflLevel K L hKL T) (eN K L hKL N htriv)),
    EqH.invariants_res_tensor (levelGal K L hKL) T (M K L hKL N htriv),
    EqH.invariants_res_eq (levelGal K L hKL) (levelGal_surjective K L hKL)]
  rfl

lemma term_N : Module.finrank (ZMod p) N.ρ.invariants =
    Module.finrank (ZMod p) (M K L hKL N htriv).ρ.invariants := by
  rw [TateK.finrank_invariants_eq_of_iso (eN K L hKL N htriv),
    EqH.invariants_res_eq (levelGal K L hKL) (levelGal_surjective K L hKL)]

lemma term_perm (Z : Type) [MulAction ↥K.fixingSubgroup Z] [Finite Z] :
    Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup Z ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      Module.finrank (ZMod p) (EqH.eqFun Z (Rep.res (levelGal K L hKL) (M K L hKL N htriv))) := by
  rw [TateK.finrank_invariants_eq_of_iso (whiskerLeftIso (Rep.ofMulActionFinsupp (ZMod p) ↥K.fixingSubgroup Z) (eN K L hKL N htriv)),
    EqH.finrank_invariants_permTensor]

end Assembly
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqHP"

end EqHP
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqHP"

namespace EqHP

local notation "Qbar" => (AlgebraicClosure ℚ)
local notation "Γ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

section Places
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes)
  (K L : IntermediateField ℚ Qbar) (hKL : K ≤ L) [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
  [Normal ↥K ↥(levelField K L hKL)] (hnorm : IsNormalLevel K L)
  (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
  (htriv : ∀ s : ↥K.fixingSubgroup, (s : Γ) ∈ L.fixingSubgroup → N.ρ s = 1)

include hnorm in
set_option maxHeartbeats 3200000 in
lemma term_arch :
    Module.finrank (ZMod p) (placesRep K L hnorm S (Sum.inl ()) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (LevelGal K L hKL)
          (Σ v : NumberField.InfinitePlace ↥K, (LevelGal K L hKL) ⧸
            NumberField.InfPlaceDecomp.decomp ↥K ↥(levelField K L hKL) (NumberField.ArchIdele.above ↥K ↥(levelField K L hKL) v)) ⊗
          M K L hKL N htriv : Rep.{0} (ZMod p) (LevelGal K L hKL)).ρ.invariants := by
  letI : MulAction ↥K.fixingSubgroup (placesAbove L S (Sum.inl ())) :=
    orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inl ())).range)
  obtain ⟨e₁, he₁⟩ := NumberField.LevelArith.exists_placesAbove_inl_equiv_infinitePlace K L hKL hnorm S
  obtain ⟨e₂, he₂⟩ := NumberField.InfPlaceDecomp.exists_equiv_sigma_quotient_decomp_above ↥K ↥(levelField K L hKL)
  haveI : Finite (placesAbove L S (Sum.inl ())) := Finite.of_equiv _ e₁.symm
  calc Module.finrank (ZMod p) (placesRep K L hnorm S (Sum.inl ()) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants
      = Module.finrank (ZMod p) (EqH.eqFun (placesAbove L S (Sum.inl ())) (Rep.res (levelGal K L hKL) (M K L hKL N htriv))) :=
        term_perm K L hKL N htriv (placesAbove L S (Sum.inl ()))
    _ = Module.finrank (ZMod p) (EqH.eqFun (NumberField.InfinitePlace ↥(levelField K L hKL)) (M K L hKL N htriv)) :=
        EqH.finrank_eqFun_transport (levelGal K L hKL) (levelGal_surjective K L hKL) e₁ he₁ _
    _ = Module.finrank (ZMod p) (EqH.eqFun (Σ v : NumberField.InfinitePlace ↥K, (LevelGal K L hKL) ⧸
            NumberField.InfPlaceDecomp.decomp ↥K ↥(levelField K L hKL) (NumberField.ArchIdele.above ↥K ↥(levelField K L hKL) v))
          (M K L hKL N htriv)) :=
        EqH.finrank_eqFun_transportId e₂ he₂ _
    _ = _ := (EqH.finrank_invariants_permTensor _ _).symm

scoped instance finite_W' (q : ↥S) : Finite ↥(EqH.W ↥(levelField K L hKL) ((q : Nat.Primes) : ℕ)) :=
  EqH.finite_W ↥(levelField K L hKL) (q : Nat.Primes).2.ne_zero

include hnorm in
set_option maxHeartbeats 3200000 in

lemma term_q (q : ↥S) :
    Module.finrank (ZMod p) (placesRep K L hnorm S (Sum.inr q) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      Module.finrank (ZMod p) (EqH.eqFun ↥(EqH.W ↥(levelField K L hKL) ((q : Nat.Primes) : ℕ)) (M K L hKL N htriv)) := by
  letI : MulAction ↥K.fixingSubgroup (placesAbove L S (Sum.inr q)) :=
    orbitQuotientAction K L hnorm (Γ ⧸ (extArithLoc S (Sum.inr q)).range)
  obtain ⟨e, hinj, hrange, he⟩ := NumberField.LevelArith.exists_placesAbove_inr_embedding_heightOneSpectrum K L hKL hnorm S q
  let e' : placesAbove L S (Sum.inr q) ≃ ↥(EqH.W ↥(levelField K L hKL) ((q : Nat.Primes) : ℕ)) :=
    (Equiv.ofInjective e hinj).trans (Equiv.setCongr hrange)
  have he' : ∀ (γ : ↥K.fixingSubgroup) (x : placesAbove L S (Sum.inr q)), e' (γ • x) = levelGal K L hKL γ • e' x :=
    fun γ x => Subtype.ext (he γ x)
  haveI : Finite (placesAbove L S (Sum.inr q)) := Finite.of_equiv _ e'.symm
  exact (term_perm K L hKL N htriv (placesAbove L S (Sum.inr q))).trans
    (EqH.finrank_eqFun_transport (levelGal K L hKL) (levelGal_surjective K L hKL) e' he' _)

omit [Normal ↥K ↥(levelField K L hKL)] in

lemma natCast_mem_unique {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime) (w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL)))
    (h : ((q : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal) (h' : ((q' : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal) : q = q' := by
  by_contra hne
  have hcop : IsCoprime ((q : 𝓞 ↥(levelField K L hKL))) ((q' : 𝓞 ↥(levelField K L hKL))) := by
    have := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne)).map (Int.castRingHom (𝓞 ↥(levelField K L hKL)))
    simpa using this
  obtain ⟨a, b, hab⟩ := hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

omit [Normal ↥K ↥(levelField K L hKL)] in
lemma under_mem_iff (w : HeightOneSpectrum (𝓞 ↥(levelField K L hKL))) :
    w ∈ NumberField.SUnits.placesAbove ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S) ↔
      ∃ q : ↥S, ((((q : Nat.Primes) : ℕ) : 𝓞 ↥(levelField K L hKL))) ∈ w.asIdeal := by
  rw [NumberField.SUnits.mem_placesAbove, mem_placesOverPrimesFinset]
  show (∃ r ∈ (S : Set Nat.Primes), (((r : ℕ) : 𝓞 ↥K)) ∈ (w.under (𝓞 ↥K)).asIdeal) ↔ _
  simp only [HeightOneSpectrum.under_asIdeal, Ideal.under, Ideal.mem_comap, map_natCast, Finset.mem_coe]
  constructor
  · rintro ⟨r, hr, h⟩; exact ⟨⟨r, hr⟩, h⟩
  · rintro ⟨r, h⟩; exact ⟨r, r.2, h⟩

noncomputable def sigmaW :
    (Σ q : ↥S, ↥(EqH.W ↥(levelField K L hKL) ((q : Nat.Primes) : ℕ))) ≃
      ↥(NumberField.SUnits.placesAbove ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S)) :=
  Equiv.ofBijective (fun x => ⟨x.2.1, (under_mem_iff S K L hKL x.2.1).2 ⟨x.1, x.2.2⟩⟩)
    ⟨by
      rintro ⟨q, w, hw⟩ ⟨q', w', hw'⟩ h
      have hww : w = w' := congrArg Subtype.val h
      subst hww
      have : q = q' := Subtype.ext (Subtype.ext (natCast_mem_unique K L hKL (q : Nat.Primes).2 (q' : Nat.Primes).2 w hw hw'))
      subst this
      rfl,
     by
      rintro ⟨w, hw⟩
      obtain ⟨q, hq⟩ := (under_mem_iff S K L hKL w).1 hw
      exact ⟨⟨q, w, hq⟩, rfl⟩⟩

lemma sigmaW_smul (σ : LevelGal K L hKL) (x : Σ q : ↥S, ↥(EqH.W ↥(levelField K L hKL) ((q : Nat.Primes) : ℕ))) :
    sigmaW S K L hKL (σ • x) = σ • sigmaW S K L hKL x := by
  obtain ⟨q, w⟩ := x
  rfl

include hnorm in
set_option maxHeartbeats 3200000 in
lemma term_fin :
    ∑ q : ↥S, Module.finrank (ZMod p)
        (placesRep K L hnorm S (Sum.inr q) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants =
      Module.finrank (ZMod p) (Rep.ofMulActionFinsupp (ZMod p) (LevelGal K L hKL)
          (Σ v : placesOverPrimesFinset ↥K S, (LevelGal K L hKL) ⧸
            NumberField.PlaceDecomp.decomp ↥K ↥(levelField K L hKL) (NumberField.PlaceAbove.above ↥K ↥(levelField K L hKL) v)) ⊗
          M K L hKL N htriv : Rep.{0} (ZMod p) (LevelGal K L hKL)).ρ.invariants := by
  obtain ⟨e₃, he₃⟩ := NumberField.PlaceTransport.exists_equiv_placesAbove_sigma_quotient_decomp_above ↥K ↥(levelField K L hKL)
    (placesOverPrimesFinset ↥K S)
  have he₃' : ∀ (σ : LevelGal K L hKL) (w : ↥(NumberField.SUnits.placesAbove ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S))),
      e₃ (σ • w) = σ • e₃ w := fun σ w => he₃ σ w (σ • w) rfl
  haveI : Finite ↥(NumberField.SUnits.placesAbove ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S)) :=
    Finite.of_equiv _ (sigmaW S K L hKL)
  simp_rw [term_q S K L hKL hnorm N htriv]
  rw [← EqH.finrank_eqFun_sigma, EqH.finrank_eqFun_transportId (sigmaW S K L hKL) (sigmaW_smul S K L hKL) _,
    EqH.finrank_eqFun_transportId e₃ he₃' _, EqH.finrank_invariants_permTensor]

end Places
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqHP"

end EqHP
p2m_reactivate "P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqH P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq.EqHP"

open EqHP in
set_option maxHeartbeats 6400000 in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hK : K.IsUnramifiedOutside S) (hL : L.IsUnramifiedOutside S)
    [FiniteDimensional ℚ ↥K] [FiniteDimensional ℚ ↥L]
    (hKL : K ≤ L) [Normal ↥K ↥(levelField K L hKL)]
    (hnorm : ∀ g ∈ K.fixingSubgroup, ∀ s ∈ L.fixingSubgroup, g * s * g⁻¹ ∈ L.fixingSubgroup)
    (hcop : (L.fixingSubgroup.relIndex K.fixingSubgroup).Coprime p)
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (hζL : ζ ∈ L)
    (h4 : p = 2 → ∃ i ∈ L, i ^ 2 = -1)
    (N : Rep.{0} (ZMod p) ↥K.fixingSubgroup) [FiniteDimensional (ZMod p) N]
    (htriv : ∀ s : ↥K.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup → N.ρ s = 1) :
    Module.finrank (ZMod p) (unitsModP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
      Module.finrank (ZMod p) N.ρ.invariants =
      Module.finrank (ZMod p) (placesRep K L hnorm S (Sum.inl ()) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
      ∑ q : ↥S, Module.finrank (ZMod p)
        (placesRep K L hnorm S (Sum.inr q) p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants +
      Module.finrank (ZMod p)
        (((Rep.trivial (ZMod p) ↥K.fixingSubgroup (ZMod p)).twist ((cycloChar p).comp K.fixingSubgroup.subtype)) ⊗ N :
          Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants := by
  have hG : (Nat.card (LevelGal K L hKL)).Coprime p := by
    rw [NumberField.LevelArith.natCard_levelGal_eq_relIndex K L hKL]; exact hcop

  have HG := NumberField.SUnits.finrank_invariants_repModP_sUnitsRep_tensor_add ↥K ↥(levelField K L hKL) hG
    (placesOverPrimesFinset ↥K S) (M K L hKL N htriv)

  have t1 : Module.finrank (ZMod p) (unitsModP K L hKL S p ⊗ N : Rep.{0} (ZMod p) ↥K.fixingSubgroup).ρ.invariants = _ :=
    term_infl K L hKL N htriv (repModP p (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S)))
  have t2 := term_N K L hKL N htriv
  have t3 := term_arch S K L hKL hnorm N htriv
  have t4 := term_fin S K L hKL hnorm N htriv
  obtain ⟨eT⟩ := NumberField.LevelArith.nonempty_inflLevel_repTorsionP_sUnitsRep_iso_twist_cycloChar (p := p) S K L hKL ζ hζ hζL
  have t5 := (TateK.finrank_invariants_eq_of_iso (whiskerRightIso eT N)).symm.trans
    (term_infl K L hKL N htriv (repTorsionP p (NumberField.SUnits.sUnitsRep ↥K ↥(levelField K L hKL) (placesOverPrimesFinset ↥K S))))
  rw [t1, t2, t3, t4, t5]
  exact HG

end S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq
end P2MW
export P2MW.S_NumberField_LevelArith_finrank_invariants_unitsModP_tensor_add_finrank_invariants_eq (solution)
