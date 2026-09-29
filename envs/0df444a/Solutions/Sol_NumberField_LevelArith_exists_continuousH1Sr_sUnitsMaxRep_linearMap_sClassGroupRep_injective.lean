-- Prove2me | solution 1 for NumberField.LevelArith.exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/22736402-4bb4-55c2-8183-0c22feba16a4

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevel
import Definitions.Def_GroupCohomology_ContinuousUnramifiedLevelMap
import Definitions.Def_NumberField_LevelArithmeticModP
import Definitions.Def_NumberField_SelmerRepModP
import Definitions.Def_NumberField_SUnitsMax
import Theorems.Thm_IntermediateField_exists_normal_isUnramifiedOutside_of_le
import Theorems.Thm_NumberField_LevelArith_normal_levelField_of_isNormalLevel
import Theorems.Thm_NumberField_exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one
import Theorems.Thm_NumberField_ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
import Theorems.Thm_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
import Theorems.Thm_NumberField_LevelArith_sUnitsMaxStable_eq_sUnitsMax
import Theorems.Thm_NumberField_LevelArith_sPrimeClasses_eq_closure
import Theorems.Thm_NumberField_existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one
import Theorems.Thm_NumberField_LevelArith_inertia_apply_eq_of_dvd_valuation
import Theorems.Thm_IntermediateField_IsUnramifiedOutside_normalClosure
import Definitions.Def_NumberField_SUnitsMax
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective
p2m_attr_erase "instance" "AlgebraicClosure.Rat.isGalois"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith"
open scoped Classical NumberField NumberField.LevelArith TensorProduct Pointwise

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option Elab.async false

p2m_open "CategoryTheory CategoryTheory.MonoidalCategory Module groupCohomology ExtCitation NumberField.LevelArith IsDedekindDomain"
open scoped Classical NumberField NumberField.LevelArith

open scoped TensorProduct Pointwise NumberField.PlaceTransport

private local instance _root_.CycBaseKummerKer.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) :=
  AlgebraicClosure.isAlgebraic ℚ
p2m_export "" "CycBaseKummerKer.isAlgebraicQbar"
private local instance _root_.CycBaseKummerKer.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  ⟨inferInstance, inferInstance⟩
p2m_export "" "CycBaseKummerKer.isAlgClosureQbar"
local instance CycBaseKummerKer.isGaloisQbar : IsGalois ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.isGalois ℚ (AlgebraicClosure ℚ)
private local instance _root_.CycBaseKummerKer.normalQbar : Normal ℚ (AlgebraicClosure ℚ) :=
  IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

p2m_export "" "CycBaseKummerKer.normalQbar"
namespace CycBaseKummerSurj

lemma levelGal_surjective (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [Normal ↥K ↥(levelField K L hKL)] : Function.Surjective (levelGal K L hKL) := by
  intro g
  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥K) (K₁ := ↥(levelField K L hKL))
    (E := AlgebraicClosure ℚ) g
  refine ⟨(IntermediateField.fixingSubgroupEquiv K).symm σ, ?_⟩
  show (AlgEquiv.restrictNormalHom _) ((IntermediateField.fixingSubgroupEquiv K)
    ((IntermediateField.fixingSubgroupEquiv K).symm σ)) = g
  rw [MulEquiv.apply_symm_apply]; exact hσ

lemma mem_fixingSubgroup_of_levelGal_eq_one (K L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hKL : K ≤ L)
    [Normal ↥K ↥(levelField K L hKL)] (γ : ↥K.fixingSubgroup) (h1 : levelGal K L hKL γ = 1) :
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ L.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro z hz
  have h := levelGal_apply_coe K L hKL γ ⟨z, (IntermediateField.mem_extendScalars hKL).2 hz⟩
  rw [h1, AlgEquiv.one_apply] at h
  exact h.symm

end CycBaseKummerSurj

noncomputable section

namespace CycBaseLES

open groupCohomology

section levels

variable {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)

lemma fixingSubgroup_normal (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [hF : Normal ℚ F] : F.fixingSubgroup.Normal := by
  refine ⟨fun s hs g => ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
  intro x hx
  have hgx : g⁻¹ x ∈ F := (IntermediateField.normal_iff_forall_map_le'.1 hF g⁻¹) ⟨x, hx, rfl⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, hs _ hgx]
  simp

abbrev levelSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ)) : Subgroup G := F.fixingSubgroup.comap r

lemma levelSubgroup_normal (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] : (levelSubgroup r F).Normal :=
  (fixingSubgroup_normal F).comap r

lemma levelSubgroup_finiteIndex (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F] [FiniteDimensional ℚ F] :
    (levelSubgroup r F).FiniteIndex := by
  haveI := fixingSubgroup_normal F
  refine ⟨fun h0 => ?_⟩
  rw [Subgroup.index_comap] at h0
  have h1 : F.fixingSubgroup.index ≠ 0 := by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]; exact Module.finrank_pos.ne'
  exact h1 (Nat.eq_zero_of_zero_dvd (h0 ▸ Subgroup.relIndex_dvd_index_of_normal F.fixingSubgroup r.range))

lemma exists_normal_level {X : Type} {f : G → X} (hf : IsLevelConstantSr₁ r S f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ F ∧
      ∀ g s, s ∈ levelSubgroup r F → f (g * s) = f g := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₀ hF₀
  exact ⟨F, hF, hN, fun g s hs => h g s (IntermediateField.fixingSubgroup_antitone hle hs)⟩

lemma exists_normal_level₂ {X : Type} {f : G × G → X} (hf : IsLevelConstantSr₂ r S f) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ F ∧
      ∀ g g' s s', s ∈ levelSubgroup r F → s' ∈ levelSubgroup r F → f (g * s, g' * s') = f (g, g') := by
  obtain ⟨F₀, hF₀, h⟩ := hf
  obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S F₀ hF₀
  exact ⟨F, hF, hN, fun g g' s s' hs hs' =>
    h g g' s s' (IntermediateField.fixingSubgroup_antitone hle hs) (IntermediateField.fixingSubgroup_antitone hle hs')⟩

lemma apply_mul_left_eq {X : Type} {f : G → X} (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (h : ∀ g s, s ∈ levelSubgroup r F → f (g * s) = f g) (g s : G) (hs : s ∈ levelSubgroup r F) : f (s * g) = f g := by
  haveI := levelSubgroup_normal r F
  have h1 : g⁻¹ * s * g ∈ levelSubgroup r F := by
    have := Subgroup.Normal.conj_mem inferInstance s hs g⁻¹
    rwa [inv_inv] at this
  have h2 := h g (g⁻¹ * s * g) h1
  rwa [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul] at h2

private lemma _root_.CycBaseLES.finite_range {X : Type} {f : G → X} (hf : IsLevelConstantSr₁ r S f) : (Set.range f).Finite := by
  obtain ⟨F, hF, hN, h⟩ := exists_normal_level r S hf
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI := levelSubgroup_normal r F
  haveI := levelSubgroup_finiteIndex r F
  haveI : Finite (G ⧸ levelSubgroup r F) := Subgroup.finite_quotient_of_finiteIndex

  let fbar : G ⧸ levelSubgroup r F → X := Quotient.lift f (fun a b hab => by
    have hab' : a⁻¹ * b ∈ levelSubgroup r F := QuotientGroup.leftRel_apply.mp hab
    have := h a (a⁻¹ * b) hab'
    rw [mul_inv_cancel_left] at this
    exact this.symm)
  have hrange : Set.range f ⊆ Set.range fbar := by
    rintro _ ⟨g, rfl⟩; exact ⟨QuotientGroup.mk g, rfl⟩
  exact (Set.finite_range fbar).subset hrange

p2m_export "CycBaseLES" "finite_range"
end levels

section smooth

variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G)

lemma exists_level_forall_fixed (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a))
    (T : Set E) (hT : T.Finite) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ F ∧
      ∀ a ∈ T, ∀ s ∈ levelSubgroup r F, E.ρ s a = a := by
  classical
  induction T, hT using Set.Finite.induction_on with
  | empty =>
    obtain ⟨F, -, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S ⊥ (IntermediateField.isUnramifiedOutside_bot S)
    exact ⟨F, hF, hN, fun a ha => absurd ha (Set.notMem_empty a)⟩
  | @insert a T haT hT ih =>
    obtain ⟨F₁, hF₁, -, h₁⟩ := ih
    obtain ⟨F₂, hF₂, h₂⟩ := hsm a
    obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (F₁ ⊔ F₂) (hF₁.sup hF₂)
    refine ⟨F, hF, hN, fun b hb s hs => ?_⟩
    rcases Set.mem_insert_iff.mp hb with rfl | hb
    · have h3 := h₂ 1 s (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle) hs)
      simp only [one_mul, map_one, Module.End.one_apply] at h3
      exact h3
    · exact h₁ b hb s (IntermediateField.fixingSubgroup_antitone (le_sup_left.trans hle) hs)

lemma isLevelConstantSr₂_d₁₂ (hsm : ∀ a : E, IsLevelConstantSr₁ r S (fun g : G => E.ρ g a)) {b : G → E}
    (hb : IsLevelConstantSr₁ r S b) : IsLevelConstantSr₂ r S ((d₁₂ E).hom b) := by
  obtain ⟨F₁, hF₁, hN₁, h₁⟩ := exists_normal_level r S hb
  obtain ⟨F₂, hF₂, -, h₂⟩ := exists_level_forall_fixed r S E hsm (Set.range b) (finite_range r S hb)
  haveI := hN₁
  refine ⟨F₁ ⊔ F₂, hF₁.sup hF₂, fun g g' s s' hs hs' => ?_⟩
  have hs₁ : s ∈ levelSubgroup r F₁ := IntermediateField.fixingSubgroup_antitone le_sup_left hs
  have hs'₁ : s' ∈ levelSubgroup r F₁ := IntermediateField.fixingSubgroup_antitone le_sup_left hs'
  have hs₂ : s ∈ levelSubgroup r F₂ := IntermediateField.fixingSubgroup_antitone le_sup_right hs
  rw [d₁₂_hom_apply, d₁₂_hom_apply]
  show E.ρ (g * s) (b (g' * s')) - b (g * s * (g' * s')) + b (g * s) = E.ρ g (b g') - b (g * g') + b g
  rw [h₁ g' s' hs'₁, h₁ g s hs₁, map_mul, Module.End.mul_apply, h₂ (b g') ⟨g', rfl⟩ s hs₂]
  congr 2

  rw [show g * s * (g' * s') = g * g' * (g'⁻¹ * s * g') * s' by group]
  haveI := levelSubgroup_normal r F₁
  have hc : g'⁻¹ * s * g' ∈ levelSubgroup r F₁ := by
    have := Subgroup.Normal.conj_mem inferInstance s hs₁ g'⁻¹; rwa [inv_inv] at this
  rw [h₁ _ s' hs'₁, h₁ _ _ hc]

variable (p : ℕ)

lemma exists_lift (hdiv : ∀ x : E, ∃ y : E, (p : k) • y = x) {c : G → E} (hc : IsLevelConstantSr₁ r S c) :
    ∃ b : G → E, IsLevelConstantSr₁ r S b ∧ ∀ g, (p : k) • b g = c g := by
  choose sec hsec using hdiv
  exact ⟨sec ∘ c, hc.comp sec, fun g => hsec (c g)⟩

lemma cocycle_level {c : G → E} (hc : c ∈ cocycles₁ E) (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ F]
    (h : ∀ g s, s ∈ levelSubgroup r F → c (g * s) = c g) :
    (∀ s ∈ levelSubgroup r F, c s = 0) ∧ ∀ g, ∀ s ∈ levelSubgroup r F, E.ρ s (c g) = c g := by
  have h0 : ∀ s ∈ levelSubgroup r F, c s = 0 := by
    intro s hs
    have h1 := h 1 s hs
    rw [one_mul, cocycles₁_map_one ⟨c, hc⟩ |> fun e => (show c 1 = 0 from e)] at h1
    exact h1
  refine ⟨h0, fun g s hs => ?_⟩
  have h1 := (mem_cocycles₁_iff c).mp hc s g
  rw [apply_mul_left_eq r F h g s hs, h0 s hs, add_zero] at h1
  exact h1.symm

end smooth

end CycBaseLES

end

noncomputable section
namespace CycBaseLES
open groupCohomology
variable {k : Type} [CommRing k] {G : Type} [Group G] (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
  (E : Rep.{0} k G)

def rep (x : ↥(continuousH1Sr r S E)) : ↥(levelCocyclesSr₁ r S E) :=
  ⟨Classical.choose ((mem_continuousH1Sr_iff r S E x.1).mp x.2), (Classical.choose_spec ((mem_continuousH1Sr_iff r S E x.1).mp x.2)).1⟩
lemma H1π_rep (x : ↥(continuousH1Sr r S E)) : (H1π E).hom (rep r S E x).1 = x.1 :=
  (Classical.choose_spec ((mem_continuousH1Sr_iff r S E x.1).mp x.2)).2
end CycBaseLES
end

noncomputable section

namespace CycBaseCAP

open groupCohomology NumberField

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ))

lemma val_apply_mul (c : ↥(cocycles₁ (sUnitsMaxRep S L))) (g h : ↥L.fixingSubgroup) :
    sUnitsMaxRep.val S L (c (g * h)) =
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • sUnitsMaxRep.val S L (c h)) * sUnitsMaxRep.val S L (c g) := by
  have h1 := (mem_cocycles₁_iff (A := sUnitsMaxRep S L) c).mp c.2 g h
  exact congrArg (fun e : sUnitsMaxRep S L => sUnitsMaxRep.val S L e) h1

lemma exists_normal_level_ge (hL : L.IsUnramifiedOutside S)
    (c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ ↥F ∧ L ≤ F ∧
      ∀ g s : ↥L.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → c.1 (g * s) = c.1 g := by
  obtain ⟨F₀, hF₀, h₀⟩ := c.2
  obtain ⟨F, hle, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (L ⊔ F₀) (hL.sup hF₀)
  exact ⟨F, hF, hN, le_sup_left.trans hle,
    fun g s hs => h₀ g s (IntermediateField.fixingSubgroup_antitone (le_sup_right.trans hle) hs)⟩

lemma val_mem_level (c : ↥(cocycles₁ (sUnitsMaxRep S L)))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F] (hLF : L ≤ F)
    (hcst : ∀ g s : ↥L.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → c (g * s) = c g)
    (g : ↥L.fixingSubgroup) : ((sUnitsMaxRep.val S L (c g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ F := by
  obtain ⟨-, hfix⟩ := CycBaseLES.cocycle_level L.fixingSubgroup.subtype (sUnitsMaxRep S L) c.2 F hcst
  rw [← InfiniteGalois.fixedField_fixingSubgroup F, IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h := hfix g ⟨σ, IntermediateField.fixingSubgroup_antitone hLF hσ⟩ hσ
  exact congrArg (fun e : sUnitsMaxRep S L => ((sUnitsMaxRep.val S L e : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h

section core

variable (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [Normal ↥L ↥(levelField L F hLF)]
  (v : ↥L.fixingSubgroup → (AlgebraicClosure ℚ)ˣ)
  (hmul : ∀ g h : ↥L.fixingSubgroup, v (g * h) = ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • v h) * v g)
  (hcst : ∀ g s : ↥L.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → v (g * s) = v g)
  (hvF : ∀ g : ↥L.fixingSubgroup, ((v g : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ F)

include hcst in
lemma v_eq_of_levelGal_eq (γ γ' : ↥L.fixingSubgroup) (h : levelGal L F hLF γ = levelGal L F hLF γ') : v γ = v γ' := by
  have h1 : levelGal L F hLF (γ⁻¹ * γ') = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
  have h2 := CycBaseKummerSurj.mem_fixingSubgroup_of_levelGal_eq_one L F hLF _ h1
  have h3 := hcst γ (γ⁻¹ * γ') h2
  have h4 : γ * (γ⁻¹ * γ') = γ' := mul_inv_cancel_left γ γ'
  rw [h4] at h3
  exact h3.symm

def uF (g : ↥L.fixingSubgroup) : (↥(levelField L F hLF))ˣ :=
  Units.mk0 ⟨_, (IntermediateField.mem_extendScalars hLF).2 (hvF g)⟩ (fun h0 => (v g).ne_zero (congrArg Subtype.val h0))

omit [Normal ↥L ↥(levelField L F hLF)] in
lemma coe_uF (g : ↥L.fixingSubgroup) : (((uF L F hLF v hvF g : (↥(levelField L F hLF))ˣ) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) = v g := rfl

include hmul hcst hvF in

set_option maxHeartbeats 6400000 in

lemma exists_coboundary [FiniteDimensional ↥L ↥(levelField L F hLF)] :
    ∃ α : (AlgebraicClosure ℚ)ˣ, (α : AlgebraicClosure ℚ) ∈ F ∧
      ∀ g : ↥L.fixingSubgroup, v g = ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • α) / α := by
  classical
  letI instMDA : MulDistribMulAction (LevelGal L F hLF) (↥(levelField L F hLF))ˣ := inferInstance
  letI instMA : MulAction (LevelGal L F hLF) (↥(levelField L F hLF))ˣ := inferInstance
  letI instSM : SMul (LevelGal L F hLF) (↥(levelField L F hLF))ˣ := inferInstance
  letI instHSM : HSMul (LevelGal L F hLF) (↥(levelField L F hLF))ˣ (↥(levelField L F hLF))ˣ := inferInstance
  have hπsurj := CycBaseKummerSurj.levelGal_surjective L F hLF
  have hu_eq : ∀ γ γ' : ↥L.fixingSubgroup, levelGal L F hLF γ = levelGal L F hLF γ' →
      uF L F hLF v hvF γ = uF L F hLF v hvF γ' := by
    intro γ γ' h; apply Units.ext; apply Subtype.ext
    rw [coe_uF, coe_uF, v_eq_of_levelGal_eq L F hLF v hcst γ γ' h]
  let f : LevelGal L F hLF → (↥(levelField L F hLF))ˣ := fun q => uF L F hLF v hvF (Function.surjInv hπsurj q)
  have hf : ∀ g, f (levelGal L F hLF g) = uF L F hLF v hvF g :=
    fun g => hu_eq _ _ (Function.surjInv_eq hπsurj (levelGal L F hLF g))
  have hcoc : IsMulCocycle₁ f := by
    intro q q'
    obtain ⟨γ, rfl⟩ := hπsurj q; obtain ⟨γ', rfl⟩ := hπsurj q'
    rw [← map_mul, hf, hf, hf]
    apply Units.ext; apply Subtype.ext
    rw [coe_uF, hmul γ γ', Units.val_mul, Units.val_mul, MulMemClass.coe_mul, coe_uF]
    congr 1
    exact (levelGal_apply_coe L F hLF γ (uF L F hLF v hvF γ' : ↥(levelField L F hLF))).symm
  obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units f hcoc
  refine ⟨Units.mk0 (((β : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)) (fun h0 => β.ne_zero (Subtype.ext h0)),
    (IntermediateField.mem_extendScalars hLF).1 (β : ↥(levelField L F hLF)).2, fun g => ?_⟩
  have h1 := hβ (levelGal L F hLF g)
  rw [hf] at h1
  have h2 := congrArg (fun w : (↥(levelField L F hLF))ˣ => ((w : ↥(levelField L F hLF)) : AlgebraicClosure ℚ)) h1
  simp only [Units.val_div_eq_div_val] at h2
  rw [coe_uF] at h2
  apply Units.ext
  rw [Units.val_div_eq_div_val, ← h2]
  show ((((levelGal L F hLF g) • β : (↥(levelField L F hLF))ˣ) : ↥(levelField L F hLF)) : AlgebraicClosure ℚ) / _ = _
  congr 1
  exact levelGal_apply_coe L F hLF g (β : ↥(levelField L F hLF))

end core

theorem exists_level_coboundary (hL : L.IsUnramifiedOutside S)
    (c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ Normal ℚ ↥F ∧ L ≤ F ∧
      (∀ g s : ↥L.fixingSubgroup, (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ∈ F.fixingSubgroup → c.1 (g * s) = c.1 g) ∧
      ∃ α : (AlgebraicClosure ℚ)ˣ, (α : AlgebraicClosure ℚ) ∈ F ∧
        ∀ g : ↥L.fixingSubgroup,
          sUnitsMaxRep.val S L (c.1 g) = ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • α) / α := by
  obtain ⟨F, hF, hN, hLF, hcst⟩ := exists_normal_level_ge S L hL c
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F := hF.1
  haveI : FiniteDimensional ℚ ↥L := hL.1
  have hnorm : IsNormalLevel L F := fun g _ s hs => (CycBaseLES.fixingSubgroup_normal F).conj_mem s hs g
  haveI : Normal ↥L ↥(levelField L F hLF) := NumberField.LevelArith.normal_levelField_of_isNormalLevel L F hLF hnorm
  refine ⟨F, hF, hN, hLF, hcst, ?_⟩
  exact exists_coboundary L F hLF (fun g => sUnitsMaxRep.val S L (c.1 g)) (val_apply_mul S L c.1)
    (fun g s hs => congrArg (sUnitsMaxRep.val S L) (hcst g s hs)) (val_mem_level S L c.1 F hLF hcst)

section overF

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)

abbrev algLF : Algebra ↥L ↥F := (IntermediateField.inclusion hLF).toRingHom.toAlgebra

lemma isScalarTower_LF : letI := algLF L F hLF; IsScalarTower ℚ ↥L ↥F := by
  letI := algLF L F hLF
  exact IsScalarTower.of_algebraMap_eq (fun x => rfl)

lemma isScalarTower_LFQ : letI := algLF L F hLF; IsScalarTower ↥L ↥F (AlgebraicClosure ℚ) := by
  letI := algLF L F hLF
  exact IsScalarTower.of_algebraMap_eq (fun x => rfl)

end overF

section valDescentProof

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥F]

lemma unit_iff_valuation_eq_one (B : ValuationSubring (AlgebraicClosure ℚ)) (v : HeightOneSpectrum (𝓞 ↥F))
    (hB : ∀ x : ↥F, (x : AlgebraicClosure ℚ) ∈ B ↔ v.valuation ↥F x ≤ 1) (x : ↥F) (hx : x ≠ 0) :
    ((x : AlgebraicClosure ℚ) ∈ B ∧ ((x : AlgebraicClosure ℚ))⁻¹ ∈ B) ↔ v.valuation ↥F x = 1 := by
  constructor
  · rintro ⟨h1, h2⟩
    apply le_antisymm ((hB x).mp h1)
    have h3 : ((x⁻¹ : ↥F) : AlgebraicClosure ℚ) ∈ B := by push_cast; exact h2
    have h4 := (hB x⁻¹).mp h3
    rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hx))] at h4
    exact h4
  · intro h
    refine ⟨(hB x).mpr h.le, ?_⟩
    have h3 : ((x⁻¹ : ↥F) : AlgebraicClosure ℚ) ∈ B := (hB x⁻¹).mpr (by rw [map_inv₀, h, inv_one])
    push_cast at h3; exact h3

lemma exists_prime_and_valuationSubring (v : HeightOneSpectrum (𝓞 ↥F)) :
    ∃ (q : Nat.Primes) (B : ValuationSubring (AlgebraicClosure ℚ)), ((q : ℕ) : 𝓞 ↥F) ∈ v.asIdeal ∧ B.LiesOverPrime (q : ℕ) ∧
      ∀ x : ↥F, (x : AlgebraicClosure ℚ) ∈ B ↔ v.valuation ↥F x ≤ 1 := by
  classical
  obtain ⟨B, hB⟩ := NumberField.exists_valuationSubring_algebraicClosure_forall_mem_iff_valuation_le_one F v
  haveI := v.isMaximal
  haveI : Finite (𝓞 ↥F ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  letI := Ideal.Quotient.field v.asIdeal
  obtain ⟨q, hq⟩ := CharP.exists (𝓞 ↥F ⧸ v.asIdeal)
  have hq0 : q ≠ 0 := CharP.char_ne_zero_of_finite (𝓞 ↥F ⧸ v.asIdeal) q
  have hqp : q.Prime := (CharP.char_is_prime_or_zero (𝓞 ↥F ⧸ v.asIdeal) q).resolve_right hq0
  have hqmem : ((q : ℕ) : 𝓞 ↥F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ q
  refine ⟨⟨q, hqp⟩, B, hqmem, ?_, hB⟩

  have hvq : v.valuation ↥F ((q : ℕ) : ↥F) < 1 := by
    rw [show ((q : ℕ) : ↥F) = algebraMap (𝓞 ↥F) ↥F ((q : ℕ) : 𝓞 ↥F) from (map_natCast _ q).symm,
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_lt_one_iff_mem _).mpr hqmem
  show ((q : ℕ) : AlgebraicClosure ℚ) ∈ B.nonunits
  rw [ValuationSubring.mem_nonunits_iff]
  have hq' : ((q : ℕ) : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hqp.ne_zero
  by_contra hle
  rw [not_lt] at hle

  have h1 : B.valuation (((q : ℕ) : AlgebraicClosure ℚ))⁻¹ ≤ 1 := by
    rw [map_inv₀]; exact inv_le_one_of_one_le₀ hle
  have h2 : (((q : ℕ) : AlgebraicClosure ℚ))⁻¹ ∈ B := (B.valuation_le_one_iff _).mp h1
  have h3 : (((((q : ℕ) : ↥F))⁻¹ : ↥F) : AlgebraicClosure ℚ) ∈ B := by push_cast; exact h2
  have h4 := (hB _).mp h3
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr (by exact_mod_cast hqp.ne_zero)))] at h4
  exact absurd hvq (not_lt.mpr h4)

theorem valDescent' [FiniteDimensional ℚ ↥L] [IsGalois ℚ ↥F] (α : (↥F)ˣ)
    (hα : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ))⁻¹ ∈ A) :
    letI := algLF L F hLF
    ∀ (w' w'' : IsDedekindDomain.HeightOneSpectrum (𝓞 ↥F)),
      w' ∉ placesOverPrimes ↥F (S : Set Nat.Primes) → w'.asIdeal.under (𝓞 ↥L) = w''.asIdeal.under (𝓞 ↥L) →
        w'.valuationOfNeZero α = w''.valuationOfNeZero α := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  haveI := isScalarTower_LFQ L F hLF
  haveI : FiniteDimensional ↥L ↥F := Module.Finite.of_restrictScalars_finite ℚ ↥L ↥F
  haveI : IsGalois ↥L ↥F := IsGalois.tower_top_of_isGalois ℚ ↥L ↥F
  intro w' w'' hS hunder

  obtain ⟨τ, hτ⟩ : ∃ τ : ↥F ≃ₐ[↥L] ↥F, w''.asIdeal.comap (galRestrict (𝓞 ↥L) ↥L ↥F (𝓞 ↥F) τ) = w'.asIdeal :=
    Ideal.exists_comap_galRestrict_eq (R := 𝓞 ↥L) (K := ↥L) (L := ↥F) (S := 𝓞 ↥F) (p := w'.asIdeal.under (𝓞 ↥L))
      ⟨w''.isPrime, ⟨hunder⟩⟩ ⟨w'.isPrime, ⟨rfl⟩⟩
  have hsm : τ⁻¹ • w'' = w' := by
    apply HeightOneSpectrum.ext
    rw [← hτ]
    ext x
    rw [NumberField.PlaceTransport.mem_smul_asIdeal_iff, inv_inv, Ideal.mem_comap]
    have h1 : galRestrict (𝓞 ↥L) ↥L ↥F (𝓞 ↥F) τ x = τ • x := by
      apply RingOfIntegers.ext
      exact algebraMap_galRestrict_apply (𝓞 ↥L) τ x
    rw [h1]

  have hv1 : w'.valuation ↥F (α : ↥F) = w''.valuation ↥F (τ (α : ↥F)) := by
    rw [← hsm, ← NumberField.PlaceTransport.valuation_smul_apply τ⁻¹ w'' (τ (α : ↥F))]
    congr 1
    exact (τ.symm_apply_apply _).symm

  obtain ⟨σ, hσ⟩ := AlgEquiv.restrictNormalHom_surjective (F := ↥L) (K₁ := ↥F) (E := AlgebraicClosure ℚ) τ
  let g : ↥L.fixingSubgroup := (IntermediateField.fixingSubgroupEquiv L).symm σ
  have hg : ∀ y : ↥F, (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (y : AlgebraicClosure ℚ) = ((τ y : ↥F) : AlgebraicClosure ℚ) := by
    intro y
    rw [← hσ]
    show σ (algebraMap ↥F (AlgebraicClosure ℚ) y) = algebraMap ↥F (AlgebraicClosure ℚ) (σ.restrictNormal ↥F y)
    exact (AlgEquiv.restrictNormal_commutes σ ↥F y).symm

  obtain ⟨q, B, hqmem, hBq, hB⟩ := exists_prime_and_valuationSubring F w''
  have hqS : q ∉ S := by
    intro hqS
    apply hS
    refine ⟨q, hqS, ?_⟩

    have h1 : ((q : ℕ) : 𝓞 ↥L) ∈ w''.asIdeal.under (𝓞 ↥L) := by
      rw [Ideal.under_def, Ideal.mem_comap, map_natCast]; exact hqmem
    rw [← hunder, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
    exact h1

  obtain ⟨h1, h2⟩ := hα g q hqS B hBq
  have hα0 : (α : ↥F) ≠ 0 := α.ne_zero
  have hτα0 : τ (α : ↥F) ≠ 0 := (map_ne_zero τ).mpr hα0
  have hunit : w''.valuation ↥F (τ (α : ↥F) / (α : ↥F)) = 1 := by
    rw [← unit_iff_valuation_eq_one F B w'' hB _ (div_ne_zero hτα0 hα0)]
    constructor
    · have : ((τ (α : ↥F) / (α : ↥F) : ↥F) : AlgebraicClosure ℚ) =
          (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) / ((α : ↥F) : AlgebraicClosure ℚ) := by
        push_cast; rw [hg]
      rw [this]; exact h1
    · have : (((τ (α : ↥F) / (α : ↥F) : ↥F) : AlgebraicClosure ℚ))⁻¹ =
          ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) / ((α : ↥F) : AlgebraicClosure ℚ))⁻¹ := by
        push_cast; rw [hg]
      rw [this]; exact h2
  have hv2 : w''.valuation ↥F (τ (α : ↥F)) = w''.valuation ↥F (α : ↥F) := by
    rw [map_div₀, div_eq_one_iff_eq ((Valuation.ne_zero_iff _).mpr hα0)] at hunit
    exact hunit

  apply WithZero.coe_inj.mp
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq]
  exact hv1.trans hv2

end valDescentProof

section classMap

open IsDedekindDomain

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]

lemma isIntegral_OLF : letI := algLF L F hLF; Algebra.IsIntegral (𝓞 ↥L) (𝓞 ↥F) := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  exact inferInstance

lemma faithfulSMul_OLF : letI := algLF L F hLF; FaithfulSMul (𝓞 ↥L) (𝓞 ↥F) := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  exact inferInstance

def primeOver (w : HeightOneSpectrum (𝓞 ↥L)) : HeightOneSpectrum (𝓞 ↥F) :=
  letI := algLF L F hLF
  haveI := isIntegral_OLF L F hLF
  haveI := faithfulSMul_OLF L F hLF
  haveI := w.isMaximal
  ⟨Classical.choose (Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 ↥F) w.asIdeal),
    (Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 ↥F) w.asIdeal)).1.isPrime,
    fun h0 => by
      have h := (Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 ↥F) w.asIdeal)).2
      rw [h0] at h
      exact w.ne_bot (by rw [h.over, Ideal.under_bot])⟩

lemma primeOver_under (w : HeightOneSpectrum (𝓞 ↥L)) :
    letI := algLF L F hLF; (primeOver L F hLF w).asIdeal.under (𝓞 ↥L) = w.asIdeal := by
  letI := algLF L F hLF
  haveI := isIntegral_OLF L F hLF
  haveI := faithfulSMul_OLF L F hLF
  haveI := w.isMaximal
  exact ((Classical.choose_spec (Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 ↥F) w.asIdeal)).2.over).symm

def expo (α : (↥F)ˣ) (w : HeightOneSpectrum (𝓞 ↥L)) : ℤ :=
  Multiplicative.toAdd ((primeOver L F hLF w).valuationOfNeZero α)

def idealOf (α : (↥F)ˣ) : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L :=
  ∏ᶠ w : HeightOneSpectrum (𝓞 ↥L), (w.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) ^ expo L F hLF α w

end classMap

section idealProof

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]

lemma finite_setOf_valuation_ne_one (x : ↥F) (hx : x ≠ 0) :
    {w' : HeightOneSpectrum (𝓞 ↥F) | w'.valuation ↥F x ≠ 1}.Finite := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥F) x
  have ha : a ≠ 0 := by rintro rfl; simp at hx
  have hb0 : (b : 𝓞 ↥F) ≠ 0 := nonZeroDivisors.ne_zero hb
  apply ((Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr ha)).union
    (Ideal.finite_factors (Ideal.span_singleton_eq_bot.not.mpr hb0))).subset
  intro w' hw'
  simp only [Set.mem_setOf_eq, Set.mem_union] at hw' ⊢
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  apply hw'
  rw [map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have e1 : w'.intValuation a = 1 := by
    apply le_antisymm (w'.intValuation_le_one a)
    rw [← not_lt, w'.intValuation_lt_one_iff_dvd]; exact h1
  have e2 : w'.intValuation b = 1 := by
    apply le_antisymm (w'.intValuation_le_one b)
    rw [← not_lt, w'.intValuation_lt_one_iff_dvd]; exact h2
  rw [e1, e2, div_one]

lemma primeOver_injective : Function.Injective (primeOver L F hLF) := by
  intro w₁ w₂ h
  apply HeightOneSpectrum.ext
  have h1 := primeOver_under L F hLF w₁
  have h2 := primeOver_under L F hLF w₂
  rw [h] at h1
  exact h1.symm.trans h2

lemma expo_eventually_eq_zero (α : (↥F)ˣ) : ∀ᶠ w : HeightOneSpectrum (𝓞 ↥L) in Filter.cofinite, expo L F hLF α w = 0 := by
  rw [Filter.eventually_cofinite]
  apply ((finite_setOf_valuation_ne_one F (α : ↥F) α.ne_zero).preimage (primeOver_injective L F hLF).injOn).subset
  intro w hw
  simp only [Set.mem_setOf_eq, Set.mem_preimage] at hw ⊢
  intro h1
  apply hw
  show Multiplicative.toAdd ((primeOver L F hLF w).valuationOfNeZero α) = 0
  have h2 : ((primeOver L F hLF w).valuationOfNeZero α : WithZero (Multiplicative ℤ)) = 1 := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq]; exact h1
  have h3 : (primeOver L F hLF w).valuationOfNeZero α = 1 := by exact_mod_cast h2
  rw [h3, toAdd_one]

lemma not_mem_placesOverPrimes_of_under (w : HeightOneSpectrum (𝓞 ↥L)) (hw : w ∉ placesOverPrimes ↥L (S : Set Nat.Primes))
    (w' : HeightOneSpectrum (𝓞 ↥F)) (hunder : letI := algLF L F hLF; w'.asIdeal.under (𝓞 ↥L) = w.asIdeal) :
    w' ∉ placesOverPrimes ↥F (S : Set Nat.Primes) := by
  letI := algLF L F hLF
  rintro ⟨q, hqS, hq⟩
  apply hw
  refine ⟨q, hqS, ?_⟩
  rw [← hunder, Ideal.under_def, Ideal.mem_comap, map_natCast]
  exact hq

lemma idealOf_ne_zero' (α : (↥F)ˣ) : idealOf L F hLF α ≠ 0 := by
  unfold idealOf
  refine finprod_induction (fun I : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L => I ≠ 0) one_ne_zero
    (fun I J hI hJ => mul_ne_zero hI hJ) (fun w => ?_)
  exact zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr w.ne_bot)

theorem idealOf_spec' [IsGalois ℚ ↥F] (α : (↥F)ˣ)
    (hα : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ))⁻¹ ∈ A) :
    letI := algLF L F hLF
    idealOf L F hLF α ≠ 0 ∧
      ∀ (w : HeightOneSpectrum (𝓞 ↥L)), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
        ∀ w' : HeightOneSpectrum (𝓞 ↥F), w'.asIdeal.under (𝓞 ↥L) = w.asIdeal →
          FractionalIdeal.count ↥L w (idealOf L F hLF α) = Multiplicative.toAdd (w'.valuationOfNeZero α) := by
  letI := algLF L F hLF
  refine ⟨idealOf_ne_zero' L F hLF α, fun w hw w' hunder => ?_⟩
  unfold idealOf
  rw [FractionalIdeal.count_finprod ↥L w _ (expo_eventually_eq_zero L F hLF α)]
  unfold expo
  congr 1
  have h1 := primeOver_under L F hLF w
  exact valDescent' S L F hLF α hα (primeOver L F hLF w) w'
    (not_mem_placesOverPrimes_of_under S L F hLF w hw _ h1) (h1.trans hunder.symm)

end idealProof

section valExt

open IsDedekindDomain NumberField UniqueFactorizationMonoid

variable (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]

lemma pow_dvd_span_iff (w : HeightOneSpectrum (𝓞 ↥L)) (w' : HeightOneSpectrum (𝓞 ↥F))
    (hunder : letI := algLF L F hLF; w'.asIdeal.under (𝓞 ↥L) = w.asIdeal)
    (he : letI := algLF L F hLF; Ideal.ramificationIdx' w.asIdeal w'.asIdeal = 1) (r : 𝓞 ↥L) (hr : r ≠ 0) (n : ℕ) :
    letI := algLF L F hLF
    w'.asIdeal ^ n ∣ Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r} ↔ w.asIdeal ^ n ∣ Ideal.span {r} := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  haveI := faithfulSMul_OLF L F hLF
  have hmapspan : Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) (Ideal.span {r}) = Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r} := by
    rw [Ideal.map_span, Set.image_singleton]
  have hmaple : Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) w.asIdeal ≤ w'.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, hunder]
  have hr' : algebraMap (𝓞 ↥L) (𝓞 ↥F) r ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hr
  have hspan0 : Ideal.span {r} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hr
  have hspan0' : Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r} ≠ ⊥ := Ideal.span_singleton_eq_bot.not.mpr hr'
  have hmapw0 : Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) w.asIdeal ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot w.ne_bot
  have hPw : Prime w.asIdeal := Ideal.prime_of_isPrime w.ne_bot w.isPrime
  have hPw' : Prime w'.asIdeal := Ideal.prime_of_isPrime w'.ne_bot w'.isPrime
  constructor
  · intro hdvd

    have hfin : FiniteMultiplicity w.asIdeal (Ideal.span {r}) :=
      FiniteMultiplicity.of_prime_left hPw hspan0
    obtain ⟨k, hk⟩ : ∃ k : ℕ, emultiplicity w.asIdeal (Ideal.span {r}) = k := ⟨_, hfin.emultiplicity_eq_multiplicity⟩
    by_cases hnk : n ≤ k
    · have h1 : w.asIdeal ^ k ∣ Ideal.span {r} := pow_dvd_iff_le_emultiplicity.mpr hk.ge
      exact (pow_dvd_pow _ hnk).trans h1
    · exfalso
      push Not at hnk

      obtain ⟨J, hJ⟩ : w.asIdeal ^ k ∣ Ideal.span {r} := pow_dvd_iff_le_emultiplicity.mpr hk.ge
      have hwJ : ¬ w.asIdeal ∣ J := by
        intro h
        have h2 : w.asIdeal ^ (k + 1) ∣ Ideal.span {r} := by
          rw [hJ, pow_succ]; exact mul_dvd_mul_left _ h
        have h3 := pow_dvd_iff_le_emultiplicity.mp h2
        rw [hk] at h3
        exact absurd (by exact_mod_cast h3 : k + 1 ≤ k) (by omega)

      have hJ' : Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r} =
          Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) w.asIdeal ^ k * Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) J := by
        rw [← hmapspan, hJ, Ideal.map_mul, Ideal.map_pow]

      have hmw : emultiplicity w'.asIdeal (Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) w.asIdeal) = 1 := by
        rw [emultiplicity_eq_count_normalizedFactors w'.irreducible hmapw0, normalize_eq,
          ← Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hmapw0 w'.isPrime w'.ne_bot, he]
        rfl
      have hmJ : emultiplicity w'.asIdeal (Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) J) = 0 := by
        rw [emultiplicity_eq_zero]
        intro h
        apply hwJ
        rw [Ideal.dvd_iff_le] at h ⊢
        rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, hunder] at h
        exact h
      have hmr : emultiplicity w'.asIdeal (Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r}) = k := by
        rw [hJ', emultiplicity_mul hPw', emultiplicity_pow hPw', hmw, hmJ, mul_one, add_zero]
      have h4 := pow_dvd_iff_le_emultiplicity.mp hdvd
      rw [hmr] at h4
      exact absurd (by exact_mod_cast h4 : n ≤ k) (by omega)
  · intro hdvd
    rw [Ideal.dvd_iff_le] at hdvd ⊢
    calc Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r}
        = Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) (Ideal.span {r}) := hmapspan.symm
      _ ≤ Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) (w.asIdeal ^ n) := Ideal.map_mono hdvd
      _ = Ideal.map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) w.asIdeal ^ n := Ideal.map_pow _ _ _
      _ ≤ w'.asIdeal ^ n := Ideal.pow_right_mono hmaple n

lemma intValuation_algebraMap_eq (w : HeightOneSpectrum (𝓞 ↥L)) (w' : HeightOneSpectrum (𝓞 ↥F))
    (hunder : letI := algLF L F hLF; w'.asIdeal.under (𝓞 ↥L) = w.asIdeal)
    (he : letI := algLF L F hLF; Ideal.ramificationIdx' w.asIdeal w'.asIdeal = 1) (r : 𝓞 ↥L) :
    letI := algLF L F hLF
    w'.intValuation (algebraMap (𝓞 ↥L) (𝓞 ↥F) r) = w.intValuation r := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  haveI := faithfulSMul_OLF L F hLF
  by_cases hr : r = 0
  · subst hr; simp
  have hr' : algebraMap (𝓞 ↥L) (𝓞 ↥F) r ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).mpr hr

  have key : ∀ n : ℕ, w'.intValuation (algebraMap (𝓞 ↥L) (𝓞 ↥F) r) ≤ WithZero.exp (-(n : ℤ)) ↔ w.intValuation r ≤ WithZero.exp (-(n : ℤ)) := by
    intro n
    rw [HeightOneSpectrum.intValuation_le_pow_iff_dvd, HeightOneSpectrum.intValuation_le_pow_iff_dvd]
    exact pow_dvd_span_iff L F hLF w w' hunder he r hr n

  obtain ⟨a, ha⟩ : ∃ a : ℕ, w'.intValuation (algebraMap (𝓞 ↥L) (𝓞 ↥F) r) = WithZero.exp (-(a : ℤ)) :=
    ⟨_, w'.intValuation_if_neg hr'⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, w.intValuation r = WithZero.exp (-(b : ℤ)) := ⟨_, w.intValuation_if_neg hr⟩
  rw [ha, hb] at key ⊢
  have h1 := (key a).mp le_rfl
  have h2 := (key b).mpr le_rfl
  rw [WithZero.exp_le_exp, neg_le_neg_iff, Nat.cast_le] at h1 h2
  congr 2
  exact_mod_cast le_antisymm h1 h2

theorem valuation_algebraMap_eq_of_ramificationIdx_eq_one'
    (w : HeightOneSpectrum (𝓞 ↥L)) (w' : HeightOneSpectrum (𝓞 ↥F))
    (hunder : letI := algLF L F hLF; w'.asIdeal.under (𝓞 ↥L) = w.asIdeal)
    (he : letI := algLF L F hLF; Ideal.ramificationIdx' w.asIdeal w'.asIdeal = 1) (x : ↥L) :
    letI := algLF L F hLF
    w'.valuation ↥F (algebraMap ↥L ↥F x) = w.valuation ↥L x := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥L) x
  rw [map_div₀, map_div₀, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]
  have e1 : algebraMap ↥L ↥F (algebraMap (𝓞 ↥L) ↥L a) = algebraMap (𝓞 ↥F) ↥F (algebraMap (𝓞 ↥L) (𝓞 ↥F) a) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  have e2 : algebraMap ↥L ↥F (algebraMap (𝓞 ↥L) ↥L (b : 𝓞 ↥L)) = algebraMap (𝓞 ↥F) ↥F (algebraMap (𝓞 ↥L) (𝓞 ↥F) (b : 𝓞 ↥L)) := by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  rw [e1, e2, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap,
    intValuation_algebraMap_eq L F hLF w w' hunder he, intValuation_algebraMap_eq L F hLF w w' hunder he]

end valExt

section eOne

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]

theorem ramificationIdx_eq_one' [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (Q : Ideal (𝓞 ↥F)) (hQ : Q.IsMaximal) (hQS : ∀ q : Nat.Primes, q ∈ S → ((q : ℕ) : 𝓞 ↥F) ∉ Q) :
    letI := algLF L F hLF
    Ideal.ramificationIdx' (Q.under (𝓞 ↥L)) Q = 1 := by
  classical

  have hQ0 : Q ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hQ (RingOfIntegers.not_isField ↥F)
  haveI : Finite (𝓞 ↥F ⧸ Q) := Ideal.finiteQuotientOfFreeOfNeBot Q hQ0
  letI := Ideal.Quotient.field Q
  obtain ⟨ℓ, hℓ⟩ := CharP.exists (𝓞 ↥F ⧸ Q)
  have hℓ0 : ℓ ≠ 0 := CharP.char_ne_zero_of_finite (𝓞 ↥F ⧸ Q) ℓ
  have hℓp : ℓ.Prime := (CharP.char_is_prime_or_zero (𝓞 ↥F ⧸ Q) ℓ).resolve_right hℓ0
  have hℓmem : ((ℓ : ℕ) : 𝓞 ↥F) ∈ Q := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact CharP.cast_eq_zero _ ℓ
  have hℓS : (⟨ℓ, hℓp⟩ : Nat.Primes) ∉ S := fun h => hQS ⟨ℓ, hℓp⟩ h hℓmem
  have hHin : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ → P.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup :=
    fun P hP => hF.2 ⟨ℓ, hℓp⟩ hℓS P hP
  exact NumberField.ramificationIdx_under_eq_one_of_forall_liesOverPrime_inertiaSubgroupIn_le_fixingSubgroup
    ↥L F (IntermediateField.inclusion hLF) ℓ hℓp hHin Q hQ hℓmem

end eOne

section asm1

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

def mkS (I : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) (hI : I ≠ 0) : sClassGroupRep ↥L ↥L (S : Set Nat.Primes) :=
  Submodule.Quotient.mk (Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 I hI)))

lemma mkS_congr {I J : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L} (hI : I ≠ 0) (hJ : J ≠ 0) (h : I = J) :
    mkS S L I hI = mkS S L J hJ := by subst h; rfl

lemma mkS_mul (I J : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) (hI : I ≠ 0) (hJ : J ≠ 0) :
    mkS S L (I * J) (mul_ne_zero hI hJ) = mkS S L I hI + mkS S L J hJ := by
  unfold mkS
  rw [show Units.mk0 (I * J) (mul_ne_zero hI hJ) = Units.mk0 I hI * Units.mk0 J hJ from Units.ext rfl, map_mul]
  exact Submodule.Quotient.mk_add _

lemma mkS_spanSingleton_mul (x : ↥L) (hx : x ≠ 0) (I : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) (hI : I ≠ 0) :
    mkS S L (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) x * I)
      (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hI) = mkS S L I hI := by
  rw [mkS_mul S L _ _ (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx) hI]
  have h1 : ClassGroup.mk ↥L (Units.mk0 (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) x)
      (FractionalIdeal.spanSingleton_ne_zero_iff.mpr hx)) = 1 := by
    rw [ClassGroup.mk_eq_one_iff]
    exact ⟨⟨x, by rw [Units.val_mk0, FractionalIdeal.coe_spanSingleton]⟩⟩
  unfold mkS
  rw [h1]
  have h0 : (Submodule.Quotient.mk (Additive.ofMul (1 : ClassGroup (𝓞 ↥L))) : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0 :=
    Submodule.Quotient.mk_zero _
  rw [h0]
  exact zero_add _

lemma mkS_eq_of_count_eq (I J : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
      FractionalIdeal.count ↥L w I = FractionalIdeal.count ↥L w J) :
    mkS S L I hI = mkS S L J hJ := by
  classical
  unfold mkS
  refine (Submodule.Quotient.eq (sPrimeClassesSubmodule ↥L ↥L (S : Set Nat.Primes))).mpr ?_
  rw [mem_sPrimeClassesSubmodule, NumberField.LevelArith.sPrimeClasses_eq_closure]

  have hQ : I * J⁻¹ ≠ 0 := mul_ne_zero hI (inv_ne_zero hJ)
  have hcountQ : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
      FractionalIdeal.count ↥L w (I * J⁻¹) = 0 := by
    intro w hw
    rw [FractionalIdeal.count_mul ↥L w hI (inv_ne_zero hJ), FractionalIdeal.count_inv, h w hw, add_neg_cancel]

  let uv : HeightOneSpectrum (𝓞 ↥L) → (FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L)ˣ := fun v =>
    Units.mk0 (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  have hsupp : (Function.mulSupport fun v => uv v ^ FractionalIdeal.count ↥L v (I * J⁻¹)).Finite := by
    apply (FractionalIdeal.finite_factors (I * J⁻¹)).subset
    intro v hv
    simp only [Function.mem_mulSupport] at hv
    intro h0
    exact hv (by rw [h0, zpow_zero])
  have hfac : Units.mk0 I hI * (Units.mk0 J hJ)⁻¹ = ∏ᶠ v, uv v ^ FractionalIdeal.count ↥L v (I * J⁻¹) := by
    apply Units.ext
    rw [show ((∏ᶠ v, uv v ^ FractionalIdeal.count ↥L v (I * J⁻¹) : (FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L)ˣ) :
        FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) = ∏ᶠ v, (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) ^
          FractionalIdeal.count ↥L v (I * J⁻¹) from by
      rw [← Units.coeHom_apply, (Units.coeHom _).map_finprod hsupp]
      exact finprod_congr fun v => by rw [map_zpow]; rfl]
    rw [FractionalIdeal.finprod_heightOneSpectrum_factorization' ↥L hQ]
    rfl
  show Additive.toMul (Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 I hI)) - Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 J hJ))) ∈ _
  rw [← ofMul_div, toMul_ofMul, ← map_div, div_eq_mul_inv, hfac, MonoidHom.map_finprod _ hsupp]
  refine finprod_induction (fun c => c ∈ Subgroup.closure (primeClass ↥L '' placesOverPrimes ↥L (S : Set Nat.Primes))) (one_mem _)
    (fun a b ha hb => mul_mem ha hb) (fun v => ?_)
  by_cases hv : v ∈ placesOverPrimes ↥L (S : Set Nat.Primes)
  · rw [map_zpow]
    apply zpow_mem
    apply Subgroup.subset_closure
    refine ⟨v, hv, ?_⟩

    show ClassGroup.mk0 _ = _
    rw [← ClassGroup.mk_mk0 ↥L]
    exact congrArg (ClassGroup.mk ↥L) (Units.ext (by rw [FractionalIdeal.coe_mk0]; rfl))
  · rw [hcountQ v hv, zpow_zero, map_one]
    exact one_mem _

end asm1

section asm2

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

abbrev liftUnit {F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F'') (α : (↥F)ˣ) : (↥F'')ˣ :=
  Units.map (IntermediateField.inclusion h : ↥F →* ↥F'') α

lemma coe_liftUnit {F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F'') (α : (↥F)ˣ) :
    (((liftUnit h α : (↥F'')ˣ) : ↥F'') : AlgebraicClosure ℚ) = ((α : ↥F) : AlgebraicClosure ℚ) := rfl

lemma hα_liftUnit {F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)} (h : F ≤ F'') (α : (↥F)ˣ)
    (hα : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ))⁻¹ ∈ A) :
    ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((((liftUnit h α : (↥F'')ˣ) : ↥F'')) : AlgebraicClosure ℚ)) /
          (((liftUnit h α : (↥F'')ˣ) : ↥F'') : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((((liftUnit h α : (↥F'')ˣ) : ↥F'')) : AlgebraicClosure ℚ)) /
          (((liftUnit h α : (↥F'')ˣ) : ↥F'') : AlgebraicClosure ℚ))⁻¹ ∈ A := hα

lemma count_idealOf_liftUnit (F F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (hFF : F ≤ F'')
    [FiniteDimensional ℚ ↥F] [FiniteDimensional ℚ ↥F''] [IsGalois ℚ ↥F] [IsGalois ℚ ↥F''] (hF'' : F''.IsUnramifiedOutside S)
    (α : (↥F)ˣ)
    (hα : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ))⁻¹ ∈ A)
    (w : HeightOneSpectrum (𝓞 ↥L)) (hw : w ∉ placesOverPrimes ↥L (S : Set Nat.Primes)) :
    FractionalIdeal.count ↥L w (idealOf L F hLF α) = FractionalIdeal.count ↥L w (idealOf L F'' (hLF.trans hFF) (liftUnit hFF α)) := by

  letI iLF := algLF L F hLF
  letI iFF := algLF F F'' hFF
  letI iLF'' := algLF L F'' (hLF.trans hFF)
  haveI : IsScalarTower ↥L ↥F ↥F'' := IsScalarTower.of_algebraMap_eq (fun x => rfl)
  haveI := isScalarTower_LF L F hLF
  haveI := isScalarTower_LF F F'' hFF
  haveI := isScalarTower_LF L F'' (hLF.trans hFF)
  haveI := isIntegral_OLF F F'' hFF

  let w'' := primeOver L F'' (hLF.trans hFF) w
  have hw''under : w''.asIdeal.under (𝓞 ↥L) = w.asIdeal := primeOver_under L F'' (hLF.trans hFF) w
  have hw''S : w'' ∉ placesOverPrimes ↥F'' (S : Set Nat.Primes) := not_mem_placesOverPrimes_of_under S L F'' (hLF.trans hFF) w hw w'' hw''under
  haveI := w''.isPrime
  let w' : HeightOneSpectrum (𝓞 ↥F) := ⟨w''.asIdeal.under (𝓞 ↥F), inferInstance,
    fun h0 => w''.ne_bot (Ideal.eq_bot_of_comap_eq_bot h0)⟩
  have hw'under : w'.asIdeal.under (𝓞 ↥L) = w.asIdeal := by
    show (w''.asIdeal.under (𝓞 ↥F)).under (𝓞 ↥L) = w.asIdeal
    rw [Ideal.under_under]; exact hw''under
  have hw'S : w' ∉ placesOverPrimes ↥F (S : Set Nat.Primes) := not_mem_placesOverPrimes_of_under S L F hLF w hw w' hw'under

  rw [(idealOf_spec' S L F hLF α hα).2 w hw w' hw'under,
    (idealOf_spec' S L F'' (hLF.trans hFF) (liftUnit hFF α) (hα_liftUnit S L hFF α hα)).2 w hw w'' hw''under]

  have he : Ideal.ramificationIdx' (w''.asIdeal.under (𝓞 ↥F)) w''.asIdeal = 1 :=
    ramificationIdx_eq_one' S F F'' hFF hF'' w''.asIdeal w''.isMaximal (fun q hqS hq => hw''S ⟨q, hqS, hq⟩)
  congr 1
  apply WithZero.coe_inj.mp
  rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq]
  exact (valuation_algebraMap_eq_of_ramificationIdx_eq_one' F F'' hFF w' w'' rfl he (α : ↥F)).symm

end asm2

section asm3

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

lemma toAdd_valuationOfNeZero_eq_neg_count_unit (w : HeightOneSpectrum (𝓞 ↥L)) (x : (↥L)ˣ) :
    Multiplicative.toAdd (w.valuationOfNeZero x) =
      -FractionalIdeal.count ↥L w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) (x : ↥L)) := by
  classical
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥L) (x : ↥L)
  have hb0 : (b : 𝓞 ↥L) ≠ 0 := nonZeroDivisors.ne_zero hb
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply x.ne_zero
    rw [← hab]; simp
  have hval : (w.valuationOfNeZero x : WithZero (Multiplicative ℤ)) = w.intValuation a / w.intValuation b := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ← hab, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
  have hspan : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) (x : ↥L) =
      FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) (algebraMap (𝓞 ↥L) ↥L a) *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) (algebraMap (𝓞 ↥L) ↥L b))⁻¹ := by
    rw [FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton, ← div_eq_mul_inv, hab]
  rw [hspan, FractionalIdeal.count_mul ↥L w (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by simpa using ha0))
    (inv_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (by simpa using hb0))), FractionalIdeal.count_inv,
    ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
    FractionalIdeal.count_coe ↥L w (Ideal.span_singleton_eq_bot.not.mpr ha0),
    FractionalIdeal.count_coe ↥L w (Ideal.span_singleton_eq_bot.not.mpr hb0)]
  rw [w.intValuation_if_neg ha0, w.intValuation_if_neg hb0, ← WithZero.exp_sub] at hval
  have h2 : w.valuationOfNeZero x = Multiplicative.ofAdd
      (-((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {a})).factors : ℤ) -
        -((Associates.mk w.asIdeal).count (Associates.mk (Ideal.span {(b : 𝓞 ↥L)})).factors : ℤ)) :=
    WithZero.coe_inj.mp (by rw [hval]; rfl)
  rw [h2, toAdd_ofAdd]
  ring

variable {S L}

structure Datum (c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) where
  F : IntermediateField ℚ (AlgebraicClosure ℚ)
  hF : F.IsUnramifiedOutside S
  gal : IsGalois ℚ ↥F
  hLF : L ≤ F
  α : (↥F)ˣ
  hcob : ∀ g : ↥L.fixingSubgroup, ((sUnitsMaxRep.val S L (c.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
    (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) / ((α : ↥F) : AlgebraicClosure ℚ)

lemma sUnitsMaxRep_unit (e : sUnitsMaxRep S L) (q : Nat.Primes) (hq : q ∉ S) (A : ValuationSubring (AlgebraicClosure ℚ))
    (hA : A.LiesOverPrime (q : ℕ)) :
    ((sUnitsMaxRep.val S L e : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A ∧
      (((sUnitsMaxRep.val S L e : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
  obtain ⟨h1, h2⟩ := (sUnitsMaxStable_le S L e.2).2 q hq A hA
  rw [Units.val_inv_eq_inv_val] at h2
  exact ⟨h1, h2⟩

namespace Datum

variable {c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))} (d : Datum c)

lemma hα : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
    ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((d.α : ↥d.F) : AlgebraicClosure ℚ)) / ((d.α : ↥d.F) : AlgebraicClosure ℚ) ∈ A ∧
    (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((d.α : ↥d.F) : AlgebraicClosure ℚ)) / ((d.α : ↥d.F) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
  intro g q hq A hA
  rw [← d.hcob g]
  exact sUnitsMaxRep_unit (c.1 g) q hq A hA

def cls [FiniteDimensional ℚ ↥L] : sClassGroupRep ↥L ↥L (S : Set Nat.Primes) :=
  haveI : FiniteDimensional ℚ ↥d.F := d.hF.1
  mkS S L (idealOf L d.F d.hLF d.α) (idealOf_ne_zero' L d.F d.hLF d.α)

lemma cls_eq [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥d.F] :
    d.cls = mkS S L (idealOf L d.F d.hLF d.α) (idealOf_ne_zero' L d.F d.hLF d.α) := rfl

end Datum

end asm3

section asm3b

open IsDedekindDomain NumberField groupCohomology

variable {S : Finset Nat.Primes} {L : IntermediateField ℚ (AlgebraicClosure ℚ)}

lemma exists_val_rel (c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
    (h : (H1π (sUnitsMaxRep S L)).hom c₁.1 = (H1π (sUnitsMaxRep S L)).hom c₂.1) :
    ∃ e₀ : sUnitsMaxRep S L, ∀ g : ↥L.fixingSubgroup,
      ((sUnitsMaxRep.val S L (c₂.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        ((sUnitsMaxRep.val S L (c₁.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) *
          ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((sUnitsMaxRep.val S L e₀ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) /
            ((sUnitsMaxRep.val S L e₀ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) := by
  have h1 : (c₂.1 : ↥L.fixingSubgroup → sUnitsMaxRep S L) - (c₁.1 : ↥L.fixingSubgroup → sUnitsMaxRep S L) ∈
      coboundaries₁ (sUnitsMaxRep S L) := (H1π_eq_iff c₂.1 c₁.1).mp h.symm
  obtain ⟨e₀, he₀⟩ := LinearMap.mem_range.mp h1
  refine ⟨e₀, fun g => ?_⟩
  have h2 : c₂.1 g = c₁.1 g + (d₀₁ (sUnitsMaxRep S L)).hom e₀ g := by
    have := congrFun he₀ g
    rw [Pi.sub_apply] at this
    rw [this]; abel
  have h3 := congrArg (fun e : sUnitsMaxRep S L => ((sUnitsMaxRep.val S L e : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)) h2
  simp only at h3
  rw [h3, d₀₁_hom_apply]
  show (((sUnitsMaxRep.val S L (c₁.1 g) * (sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ g e₀) / sUnitsMaxRep.val S L e₀) :
    (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ) = _
  rw [Units.val_mul, Units.val_div_eq_div_val, sUnitsMaxRep.val_ρ]
  rfl

lemma exists_common_level (hL : L.IsUnramifiedOutside S) {c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))}
    (d₁ : Datum c₁) (d₂ : Datum c₂) (e₀ : sUnitsMaxRep S L) :
    ∃ F'' : IntermediateField ℚ (AlgebraicClosure ℚ), F''.IsUnramifiedOutside S ∧ IsGalois ℚ ↥F'' ∧ d₁.F ≤ F'' ∧ d₂.F ≤ F'' ∧
      ((sUnitsMaxRep.val S L e₀ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ F'' := by
  obtain ⟨⟨Fε, hFε, hεF⟩, -⟩ := sUnitsMaxStable_le S L e₀.2
  obtain ⟨F'', hle, hF'', hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (d₁.F ⊔ d₂.F ⊔ Fε) ((d₁.hF.sup d₂.hF).sup hFε)
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F'' := hF''.1
  exact ⟨F'', hF'', ⟨⟩, (le_sup_left.trans le_sup_left).trans hle, (le_sup_right.trans le_sup_left).trans hle,
    (le_sup_right.trans hle) hεF⟩

lemma ratio_mem [FiniteDimensional ℚ ↥L] {c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))}
    (d₁ : Datum c₁) (d₂ : Datum c₂) (ε : (AlgebraicClosure ℚ)ˣ)
    (hrel : ∀ g : ↥L.fixingSubgroup,
      ((sUnitsMaxRep.val S L (c₂.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
        ((sUnitsMaxRep.val S L (c₁.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) *
          ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (ε : AlgebraicClosure ℚ) / (ε : AlgebraicClosure ℚ))) :
    ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) / (((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) * (ε : AlgebraicClosure ℚ)) ∈ L := by
  suffices hfix : ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) / (((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) * (ε : AlgebraicClosure ℚ)) ∈
      IntermediateField.fixedField L.fixingSubgroup by
    rwa [InfiniteGalois.fixedField_fixingSubgroup] at hfix
  rw [IntermediateField.mem_fixedField_iff]
  intro σ hσ
  have h1 := hrel ⟨σ, hσ⟩
  rw [d₁.hcob, d₂.hcob] at h1

  have hα₁ : ((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d₁.α.ne_zero (Subtype.ext h0)
  have hα₂ : ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d₂.α.ne_zero (Subtype.ext h0)
  have hε : (ε : AlgebraicClosure ℚ) ≠ 0 := ε.ne_zero
  have hσα₁ : σ ((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero σ).mpr hα₁
  have hσε : σ (ε : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero σ).mpr hε
  change σ _ / _ = σ _ / _ * (σ _ / _) at h1
  rw [map_div₀, map_mul]
  field_simp
  field_simp at h1
  linear_combination h1

end asm3b

section asm3c

open IsDedekindDomain NumberField groupCohomology

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

lemma count_idealOf_rel (F'' : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F'') [FiniteDimensional ℚ ↥F''] [IsGalois ℚ ↥F'']
    (hF'' : F''.IsUnramifiedOutside S) (a₁ a₂ e : (↥F'')ˣ) (βL : (↥L)ˣ)
    (hα₁ : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((a₁ : ↥F'') : AlgebraicClosure ℚ)) / ((a₁ : ↥F'') : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((a₁ : ↥F'') : AlgebraicClosure ℚ)) / ((a₁ : ↥F'') : AlgebraicClosure ℚ))⁻¹ ∈ A)
    (hα₂ : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((a₂ : ↥F'') : AlgebraicClosure ℚ)) / ((a₂ : ↥F'') : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((a₂ : ↥F'') : AlgebraicClosure ℚ)) / ((a₂ : ↥F'') : AlgebraicClosure ℚ))⁻¹ ∈ A)
    (he : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((e : ↥F'') : AlgebraicClosure ℚ) ∈ A ∧ (((e : ↥F'') : AlgebraicClosure ℚ))⁻¹ ∈ A)
    (hrel : a₂ = a₁ * e * liftUnit hLF βL)
    (w : HeightOneSpectrum (𝓞 ↥L)) (hw : w ∉ placesOverPrimes ↥L (S : Set Nat.Primes)) :
    FractionalIdeal.count ↥L w (idealOf L F'' hLF a₂) =
      FractionalIdeal.count ↥L w (idealOf L F'' hLF a₁) - FractionalIdeal.count ↥L w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) (βL : ↥L)) := by
  letI := algLF L F'' hLF
  let w'' := primeOver L F'' hLF w
  have hunder : w''.asIdeal.under (𝓞 ↥L) = w.asIdeal := primeOver_under L F'' hLF w
  have hw''S : w'' ∉ placesOverPrimes ↥F'' (S : Set Nat.Primes) := not_mem_placesOverPrimes_of_under S L F'' hLF w hw w'' hunder
  rw [(idealOf_spec' S L F'' hLF a₂ hα₂).2 w hw w'' hunder, (idealOf_spec' S L F'' hLF a₁ hα₁).2 w hw w'' hunder, hrel,
    map_mul, toAdd_mul, map_mul, toAdd_mul]

  have he0 : Multiplicative.toAdd (w''.valuationOfNeZero e) = 0 := by
    obtain ⟨q, B, hqmem, hBq, hB⟩ := exists_prime_and_valuationSubring F'' w''
    have hqS : q ∉ S := fun hqS => hw''S ⟨q, hqS, hqmem⟩
    have h1 : w''.valuation ↥F'' (e : ↥F'') = 1 := (unit_iff_valuation_eq_one F'' B w'' hB (e : ↥F'') e.ne_zero).mp (he q hqS B hBq)
    have h2 : w''.valuationOfNeZero e = 1 := by
      apply WithZero.coe_inj.mp; rw [HeightOneSpectrum.valuationOfNeZero_eq, h1]; rfl
    rw [h2, toAdd_one]

  have hb : Multiplicative.toAdd (w''.valuationOfNeZero (liftUnit hLF βL)) =
      -FractionalIdeal.count ↥L w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) (βL : ↥L)) := by
    rw [← toAdd_valuationOfNeZero_eq_neg_count_unit L w βL]
    congr 1
    apply WithZero.coe_inj.mp
    rw [HeightOneSpectrum.valuationOfNeZero_eq, HeightOneSpectrum.valuationOfNeZero_eq]
    have he1 : Ideal.ramificationIdx' (w''.asIdeal.under (𝓞 ↥L)) w''.asIdeal = 1 :=
      ramificationIdx_eq_one' S L F'' hLF hF'' w''.asIdeal w''.isMaximal (fun q hqS hq => hw''S ⟨q, hqS, hq⟩)
    rw [hunder] at he1
    exact valuation_algebraMap_eq_of_ramificationIdx_eq_one' L F'' hLF w w'' hunder he1 (βL : ↥L)
  rw [he0, hb]
  ring

variable {S L}

theorem Datum.cls_eq_of_H1π_eq (hL : L.IsUnramifiedOutside S)
    {c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))} (d₁ : Datum c₁) (d₂ : Datum c₂)
    (h : (H1π (sUnitsMaxRep S L)).hom c₁.1 = (H1π (sUnitsMaxRep S L)).hom c₂.1) : d₁.cls = d₂.cls := by
  classical
  haveI : FiniteDimensional ℚ ↥d₁.F := d₁.hF.1
  haveI : FiniteDimensional ℚ ↥d₂.F := d₂.hF.1
  haveI := d₁.gal
  haveI := d₂.gal
  obtain ⟨e₀, hrel⟩ := exists_val_rel c₁ c₂ h
  obtain ⟨F'', hF'', hgal, h₁, h₂, hεF⟩ := exists_common_level hL d₁ d₂ e₀
  haveI := hgal
  haveI : FiniteDimensional ℚ ↥F'' := hF''.1
  have hLF'' : L ≤ F'' := d₁.hLF.trans h₁

  set ε : (AlgebraicClosure ℚ)ˣ := sUnitsMaxRep.val S L e₀ with hεdef
  have hβmem := ratio_mem d₁ d₂ ε hrel
  have hα₁ : ((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d₁.α.ne_zero (Subtype.ext h0)
  have hα₂ : ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d₂.α.ne_zero (Subtype.ext h0)
  have hβ0 : ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) / (((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) * (ε : AlgebraicClosure ℚ)) ≠ 0 :=
    div_ne_zero hα₂ (mul_ne_zero hα₁ ε.ne_zero)
  let βL : (↥L)ˣ := Units.mk0 ⟨_, hβmem⟩ (fun h0 => hβ0 (congrArg Subtype.val h0))

  let a₁ : (↥F'')ˣ := liftUnit h₁ d₁.α
  let a₂ : (↥F'')ˣ := liftUnit h₂ d₂.α
  let e : (↥F'')ˣ := Units.mk0 ⟨(ε : AlgebraicClosure ℚ), hεF⟩ (fun h0 => ε.ne_zero (congrArg Subtype.val h0))
  have hrelu : a₂ = a₁ * e * liftUnit hLF'' βL := by
    apply Units.ext; apply Subtype.ext
    show ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) =
      ((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) * (ε : AlgebraicClosure ℚ) *
        (((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) / (((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) * (ε : AlgebraicClosure ℚ)))
    field_simp
  have he : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((e : ↥F'') : AlgebraicClosure ℚ) ∈ A ∧ (((e : ↥F'') : AlgebraicClosure ℚ))⁻¹ ∈ A :=
    fun q hq A hA => sUnitsMaxRep_unit e₀ q hq A hA

  have hcount : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
      FractionalIdeal.count ↥L w (idealOf L d₂.F d₂.hLF d₂.α) =
        FractionalIdeal.count ↥L w (idealOf L d₁.F d₁.hLF d₁.α *
          FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) ((βL⁻¹ : (↥L)ˣ) : ↥L)) := by
    intro w hw
    rw [count_idealOf_liftUnit S L d₂.F F'' d₂.hLF h₂ hF'' d₂.α d₂.hα w hw,
      count_idealOf_rel S L F'' hLF'' hF'' a₁ a₂ e βL (hα_liftUnit S L h₁ d₁.α d₁.hα) (hα_liftUnit S L h₂ d₂.α d₂.hα) he hrelu w hw,
      ← count_idealOf_liftUnit S L d₁.F F'' d₁.hLF h₁ hF'' d₁.α d₁.hα w hw,
      FractionalIdeal.count_mul ↥L w (idealOf_ne_zero' L d₁.F d₁.hLF d₁.α)
        (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)),
      Units.val_inv_eq_inv_val, ← FractionalIdeal.spanSingleton_inv, FractionalIdeal.count_inv]
    ring
  rw [d₂.cls_eq, mkS_eq_of_count_eq S L _ _ (idealOf_ne_zero' L d₂.F d₂.hLF d₂.α)
      (mul_ne_zero (idealOf_ne_zero' L d₁.F d₁.hLF d₁.α) (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _))) hcount,
    mkS_congr S L _ (mul_ne_zero (FractionalIdeal.spanSingleton_ne_zero_iff.mpr (Units.ne_zero _)) (idealOf_ne_zero' L d₁.F d₁.hLF d₁.α))
      (mul_comm _ _),
    mkS_spanSingleton_mul S L _ (Units.ne_zero _) _ (idealOf_ne_zero' L d₁.F d₁.hLF d₁.α), d₁.cls_eq]

end asm3c

section asm4

open IsDedekindDomain NumberField groupCohomology

variable {S : Finset Nat.Primes} {L : IntermediateField ℚ (AlgebraicClosure ℚ)} [FiniteDimensional ℚ ↥L]

set_option maxHeartbeats 6400000 in

lemma nonempty_datum (hL : L.IsUnramifiedOutside S) (c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) :
    Nonempty (Datum c) := by
  obtain ⟨F, hF, hN, hLF, -, α, hαF, hcob⟩ := exists_level_coboundary S L hL c
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F := hF.1
  refine ⟨⟨F, hF, ⟨⟩, hLF, Units.mk0 ⟨(α : AlgebraicClosure ℚ), hαF⟩ (fun h0 => α.ne_zero (congrArg Subtype.val h0)), fun g => ?_⟩⟩
  rw [hcob g, Units.val_div_eq_div_val]
  rfl

def datum₀ (hL : L.IsUnramifiedOutside S) (c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) : Datum c :=
  (nonempty_datum hL c).some

set_option maxHeartbeats 6400000 in

lemma exists_datum_zero (hL : L.IsUnramifiedOutside S) :
    ∃ d : Datum (0 : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))), d.α = 1 := by
  obtain ⟨F, hLF, hF, hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S L hL
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F := hF.1
  refine ⟨⟨F, hF, ⟨⟩, hLF, 1, fun g => ?_⟩, rfl⟩
  rw [Units.val_one, OneMemClass.coe_one, map_one, div_one]
  rfl

set_option maxHeartbeats 6400000 in

lemma exists_datum_add (hL : L.IsUnramifiedOutside S) {c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))}
    (d₁ : Datum c₁) (d₂ : Datum c₂) :
    ∃ (d : Datum (c₁ + c₂)) (h₁ : d₁.F ≤ d.F) (h₂ : d₂.F ≤ d.F), d.α = liftUnit h₁ d₁.α * liftUnit h₂ d₂.α := by
  obtain ⟨F'', hle, hF'', hN⟩ := IntermediateField.exists_normal_isUnramifiedOutside_of_le S (d₁.F ⊔ d₂.F) (d₁.hF.sup d₂.hF)
  haveI := hN
  haveI : FiniteDimensional ℚ ↥F'' := hF''.1
  have h₁ : d₁.F ≤ F'' := le_sup_left.trans hle
  have h₂ : d₂.F ≤ F'' := le_sup_right.trans hle
  refine ⟨⟨F'', hF'', ⟨⟩, d₁.hLF.trans h₁, liftUnit h₁ d₁.α * liftUnit h₂ d₂.α, fun g => ?_⟩, h₁, h₂, rfl⟩
  have e1 : ((sUnitsMaxRep.val S L ((c₁ + c₂).1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((sUnitsMaxRep.val S L (c₁.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) *
        ((sUnitsMaxRep.val S L (c₂.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := rfl
  rw [e1, d₁.hcob, d₂.hcob, Units.val_mul, MulMemClass.coe_mul, coe_liftUnit, coe_liftUnit, map_mul]
  have hα₁ : ((d₁.α : ↥d₁.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d₁.α.ne_zero (Subtype.ext h0)
  have hα₂ : ((d₂.α : ↥d₂.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d₂.α.ne_zero (Subtype.ext h0)
  field_simp

variable (S L)

def fXfun (hL : L.IsUnramifiedOutside S) (x : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) :
    sClassGroupRep ↥L ↥L (S : Set Nat.Primes) :=
  (datum₀ hL (CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) x)).cls

set_option maxHeartbeats 6400000 in

lemma fXfun_eq (hL : L.IsUnramifiedOutside S) (x : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)))
    {c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))} (d : Datum c)
    (hc : (H1π (sUnitsMaxRep S L)).hom c.1 = x.1) : fXfun S L hL x = d.cls :=
  Datum.cls_eq_of_H1π_eq hL _ d ((CycBaseLES.H1π_rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) x).trans hc.symm)

set_option maxHeartbeats 6400000 in
lemma fXfun_zero (hL : L.IsUnramifiedOutside S) : fXfun S L hL 0 = 0 := by
  obtain ⟨d, hd⟩ := exists_datum_zero (S := S) (L := L) hL
  haveI : FiniteDimensional ℚ ↥d.F := d.hF.1
  haveI := d.gal
  rw [fXfun_eq S L hL 0 d (by exact (map_zero _)), d.cls_eq]
  have h1 : mkS S L (idealOf L d.F d.hLF d.α) (idealOf_ne_zero' L d.F d.hLF d.α) = mkS S L 1 one_ne_zero := by
    apply mkS_eq_of_count_eq
    intro w hw
    letI := algLF L d.F d.hLF
    rw [(idealOf_spec' S L d.F d.hLF d.α d.hα).2 w hw (primeOver L d.F d.hLF w) (primeOver_under L d.F d.hLF w), hd, map_one,
      toAdd_one, FractionalIdeal.count_one]
  rw [h1]
  unfold mkS
  rw [show Units.mk0 (1 : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) one_ne_zero = 1 from Units.ext rfl, map_one]
  exact Submodule.Quotient.mk_zero _

set_option maxHeartbeats 6400000 in

lemma count_idealOf_datum_add {c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))}
    (d₁ : Datum c₁) (d₂ : Datum c₂) (d : Datum (c₁ + c₂)) (h₁ : d₁.F ≤ d.F) (h₂ : d₂.F ≤ d.F)
    (hd : d.α = liftUnit h₁ d₁.α * liftUnit h₂ d₂.α)
    [FiniteDimensional ℚ ↥d.F] [FiniteDimensional ℚ ↥d₁.F] [FiniteDimensional ℚ ↥d₂.F] [IsGalois ℚ ↥d.F] [IsGalois ℚ ↥d₁.F] [IsGalois ℚ ↥d₂.F]
    (w : HeightOneSpectrum (𝓞 ↥L)) (hw : w ∉ placesOverPrimes ↥L (S : Set Nat.Primes)) :
    FractionalIdeal.count ↥L w (idealOf L d.F d.hLF d.α) =
      FractionalIdeal.count ↥L w (idealOf L d₁.F d₁.hLF d₁.α) + FractionalIdeal.count ↥L w (idealOf L d₂.F d₂.hLF d₂.α) := by
  letI := algLF L d.F d.hLF
  have e0 := (idealOf_spec' S L d.F d.hLF d.α d.hα).2 w hw (primeOver L d.F d.hLF w) (primeOver_under L d.F d.hLF w)
  have e1 := count_idealOf_liftUnit S L d₁.F d.F d₁.hLF h₁ d.hF d₁.α d₁.hα w hw
  have e2 := count_idealOf_liftUnit S L d₂.F d.F d₂.hLF h₂ d.hF d₂.α d₂.hα w hw
  have e1' := (idealOf_spec' S L d.F (d₁.hLF.trans h₁) (liftUnit h₁ d₁.α) (hα_liftUnit S L h₁ d₁.α d₁.hα)).2 w hw
    (primeOver L d.F d.hLF w) (primeOver_under L d.F d.hLF w)
  have e2' := (idealOf_spec' S L d.F (d₂.hLF.trans h₂) (liftUnit h₂ d₂.α) (hα_liftUnit S L h₂ d₂.α d₂.hα)).2 w hw
    (primeOver L d.F d.hLF w) (primeOver_under L d.F d.hLF w)
  have hv := congrArg (fun u : (↥d.F)ˣ => Multiplicative.toAdd ((primeOver L d.F d.hLF w).valuationOfNeZero u)) hd
  simp only [map_mul, toAdd_mul] at hv
  omega

set_option maxHeartbeats 6400000 in

lemma cls_datum_add {c₁ c₂ : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L))}
    (d₁ : Datum c₁) (d₂ : Datum c₂) (d : Datum (c₁ + c₂)) (h₁ : d₁.F ≤ d.F) (h₂ : d₂.F ≤ d.F)
    (hd : d.α = liftUnit h₁ d₁.α * liftUnit h₂ d₂.α) : d.cls = d₁.cls + d₂.cls := by
  haveI : FiniteDimensional ℚ ↥d.F := d.hF.1
  haveI : FiniteDimensional ℚ ↥d₁.F := d₁.hF.1
  haveI : FiniteDimensional ℚ ↥d₂.F := d₂.hF.1
  haveI := d.gal; haveI := d₁.gal; haveI := d₂.gal
  rw [d.cls_eq, d₁.cls_eq, d₂.cls_eq, ← mkS_mul]
  apply mkS_eq_of_count_eq
  intro w hw
  rw [FractionalIdeal.count_mul ↥L w (idealOf_ne_zero' L d₁.F d₁.hLF d₁.α) (idealOf_ne_zero' L d₂.F d₂.hLF d₂.α)]
  exact count_idealOf_datum_add S L d₁ d₂ d h₁ h₂ hd w hw

set_option maxHeartbeats 6400000 in
lemma fXfun_add (hL : L.IsUnramifiedOutside S) (x y : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L))) :
    fXfun S L hL (x + y) = fXfun S L hL x + fXfun S L hL y := by
  obtain ⟨d, h₁, h₂, hd⟩ := exists_datum_add hL (datum₀ hL (CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) x))
    (datum₀ hL (CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) y))
  have hc : (H1π (sUnitsMaxRep S L)).hom ((CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) x) +
      (CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) y)).1 = (x + y).1 := by
    show (H1π (sUnitsMaxRep S L)).hom ((CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) x).1 +
        (CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) y).1) = x.1 + y.1
    rw [map_add, CycBaseLES.H1π_rep, CycBaseLES.H1π_rep]
  rw [fXfun_eq S L hL (x + y) d hc, cls_datum_add S L _ _ d h₁ h₂ hd]
  rfl

def fX (hL : L.IsUnramifiedOutside S) : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) →+ sClassGroupRep ↥L ↥L (S : Set Nat.Primes) where
  toFun := fXfun S L hL
  map_zero' := fXfun_zero S L hL
  map_add' := fXfun_add S L hL

end asm4

end CycBaseCAP
namespace CapInj

section L1
variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

lemma exists_eq_spanSingleton_mul_of_mk_eq (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ)
    (h : ClassGroup.mk K I = ClassGroup.mk K J) :
    ∃ x : K, x ≠ 0 ∧ (I : FractionalIdeal (nonZeroDivisors R) K) = FractionalIdeal.spanSingleton (nonZeroDivisors R) x * J := by
  have h1 : ClassGroup.mk K (I * J⁻¹) = 1 := by rw [map_mul, map_inv, h, mul_inv_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  refine ⟨x, fun hx0 => ?_, ?_⟩
  · rw [hx0, FractionalIdeal.spanSingleton_zero] at hx
    exact (I * J⁻¹).ne_zero hx
  · have : ((I * J⁻¹ : (FractionalIdeal (nonZeroDivisors R) K)ˣ) : FractionalIdeal (nonZeroDivisors R) K) * J = I := by
      rw [Units.val_mul, Units.inv_mul_cancel_right]
    rw [← this, hx]

lemma valuation_eq_exp_neg_count (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x = WithZero.exp (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton (nonZeroDivisors R) x))) := by
  obtain ⟨r, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hx
    exact hx rfl
  have hsK : algebraMap R K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have hI : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r / algebraMap R K s) ≠ 0 := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hx
  have heq : FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K r / algebraMap R K s) =
      FractionalIdeal.spanSingleton (nonZeroDivisors R) (algebraMap R K s)⁻¹ * ((Ideal.span {r} : Ideal R) : FractionalIdeal (nonZeroDivisors R) K) := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.spanSingleton_mul_spanSingleton, div_eq_inv_mul]
  rw [FractionalIdeal.count_well_defined K v hI heq, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.valuation_of_algebraMap, v.intValuation_if_neg hr0, v.intValuation_if_neg hs0, ← WithZero.exp_sub]
  congr 1
  push_cast
  ring

end L1

section L3
variable (F : Type) [Field F] [NumberField F] (S : Set Nat.Primes)

lemma exists_sSupported_of_mem_closure (c : ClassGroup (𝓞 F))
    (hc : c ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S)) :
    ∃ I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ, ClassGroup.mk F I = c ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ placesOverPrimes F S → FractionalIdeal.count F w (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0 := by
  induction hc using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w₀, hw₀, rfl⟩ := hx
    refine ⟨FractionalIdeal.mk0 F ⟨w₀.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 (by simpa using w₀.ne_bot)⟩, ?_, fun w hw => ?_⟩
    · rw [ClassGroup.mk_mk0]; rfl
    · have hne : w₀ ≠ w := fun h => hw (h ▸ hw₀)
      rw [FractionalIdeal.coe_mk0]
      exact FractionalIdeal.count_maximal_coprime F w hne
  | one => exact ⟨1, map_one _, fun w _ => by rw [Units.val_one, FractionalIdeal.count_one]⟩
  | mul x y _ _ hx hy =>
    obtain ⟨I, rfl, hI⟩ := hx
    obtain ⟨J, rfl, hJ⟩ := hy
    refine ⟨I * J, map_mul _ _ _, fun w hw => ?_⟩
    rw [Units.val_mul, FractionalIdeal.count_mul F w I.ne_zero J.ne_zero, hI w hw, hJ w hw, add_zero]
  | inv x _ hx =>
    obtain ⟨I, rfl, hI⟩ := hx
    refine ⟨I⁻¹, map_inv _ _, fun w hw => ?_⟩
    rw [Units.val_inv_eq_inv_val, FractionalIdeal.count_inv, hI w hw, neg_zero]

end L3

end CapInj

namespace CapInj

section L4
variable {R T : Type} [CommRing R] [IsDedekindDomain R] [CommRing T] [IsDedekindDomain T] [Algebra R T]
  [Algebra.IsIntegral R T] [Module.IsTorsionFree R T]
  (KR : Type) [Field KR] [Algebra R KR] [IsFractionRing R KR]
  (KT : Type) [Field KT] [Algebra T KT] [IsFractionRing T KT]

noncomputable def underv (P : HeightOneSpectrum T) : HeightOneSpectrum R :=
  ⟨P.asIdeal.under R, Ideal.IsPrime.under R P.asIdeal, fun h => P.ne_bot (Ideal.eq_bot_of_comap_eq_bot h)⟩

lemma underv_asIdeal (P : HeightOneSpectrum T) : (underv (R := R) P).asIdeal = P.asIdeal.under R := rfl

lemma mem_primesOver_iff (p : HeightOneSpectrum R) (P : HeightOneSpectrum T) :
    P.asIdeal ∈ p.asIdeal.primesOver T ↔ P.asIdeal.under R = p.asIdeal := by
  constructor
  · intro h; exact h.2.over.symm
  · intro h; exact ⟨P.isPrime, ⟨h.symm⟩⟩

lemma count_map_prime (p : HeightOneSpectrum R) (P : HeightOneSpectrum T) :
    FractionalIdeal.count KT P ((p.asIdeal.map (algebraMap R T) : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) =
      if P.asIdeal.under R = p.asIdeal then (p.asIdeal.ramificationIdx' P.asIdeal : ℤ) else 0 := by
  haveI := p.isMaximal
  have hp0 : p.asIdeal ≠ 0 := by simpa using p.ne_bot
  rw [Ideal.map_algebraMap_eq_finsetProd_pow hp0,
    Finset.prod_congr rfl (fun Q hQ => by
      haveI := (Set.mem_toFinset.mp hQ).1; haveI := (Set.mem_toFinset.mp hQ).2
      rw [← Ideal.ramificationIdx'_eq_ramificationIdx p.asIdeal Q p.ne_bot]),
    show (((∏ Q ∈ (p.asIdeal.primesOver T).toFinset, Q ^ p.asIdeal.ramificationIdx' Q : Ideal T)) : FractionalIdeal (nonZeroDivisors T) KT) =
      ∏ Q ∈ (p.asIdeal.primesOver T).toFinset, (FractionalIdeal.coeIdealHom (nonZeroDivisors T) KT) (Q ^ p.asIdeal.ramificationIdx' Q) from
      map_prod (FractionalIdeal.coeIdealHom (nonZeroDivisors T) KT) _ _, FractionalIdeal.count_prod]
  · simp only [FractionalIdeal.coeIdealHom_apply, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_pow]

    have hterm : ∀ Q ∈ (p.asIdeal.primesOver T).toFinset,
        (p.asIdeal.ramificationIdx' Q : ℤ) * FractionalIdeal.count KT P ((Q : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) =
          if Q = P.asIdeal then (p.asIdeal.ramificationIdx' P.asIdeal : ℤ) else 0 := by
      intro Q hQ
      rw [Set.mem_toFinset] at hQ
      by_cases hQP : Q = P.asIdeal
      · subst hQP; rw [if_pos rfl, FractionalIdeal.count_self, mul_one]
      · rw [if_neg hQP]
        let Qv : HeightOneSpectrum T := ⟨Q, hQ.1, Ideal.ne_bot_of_mem_primesOver (p.ne_bot) hQ⟩
        have hne : Qv ≠ P := fun h => hQP (congrArg HeightOneSpectrum.asIdeal h)
        have := FractionalIdeal.count_maximal_coprime KT P hne
        rw [show ((Q : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) = ((Qv.asIdeal : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) from rfl,
          this, mul_zero]
    rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq']
    by_cases hP : P.asIdeal.under R = p.asIdeal
    · rw [if_pos hP, if_pos]
      rw [Set.mem_toFinset]; exact (mem_primesOver_iff p P).2 hP
    · rw [if_neg hP, if_neg]
      rw [Set.mem_toFinset]; exact fun h => hP ((mem_primesOver_iff p P).1 h)
  · intro Q hQ
    rw [Set.mem_toFinset] at hQ
    simp only [FractionalIdeal.coeIdealHom_apply, Ne, FractionalIdeal.coeIdeal_eq_zero, ← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by simpa [Ideal.zero_eq_bot] using Ideal.ne_bot_of_mem_primesOver p.ne_bot hQ)

lemma count_map (P : HeightOneSpectrum T) (I : Ideal R) (hI : I ≠ 0) :
    FractionalIdeal.count KT P ((I.map (algebraMap R T) : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) =
      ((P.asIdeal.under R).ramificationIdx' P.asIdeal : ℤ) *
        FractionalIdeal.count KR (underv (R := R) P) (I : FractionalIdeal (nonZeroDivisors R) KR) := by
  induction I using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hI
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    rw [Ideal.map_top, FractionalIdeal.coeIdeal_top, FractionalIdeal.coeIdeal_top, FractionalIdeal.count_one, FractionalIdeal.count_one, mul_zero]
  | h₃ a q ha hq ih =>
    have hq0 : q ≠ ⊥ := hq.ne_zero
    have hmap0 : ∀ J : Ideal R, J ≠ 0 → ((J.map (algebraMap R T) : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) ≠ 0 := by
      intro J hJ
      rw [Ne, FractionalIdeal.coeIdeal_eq_zero, ← Ne]
      exact (Ideal.map_eq_bot_iff_of_injective (FaithfulSMul.algebraMap_injective R T)).not.2 hJ
    rw [Ideal.map_mul, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_mul,
      FractionalIdeal.count_mul KT P (hmap0 q hq0) (hmap0 a ha),
      FractionalIdeal.count_mul KR (underv (R := R) P) (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact hq0)
        (by rw [Ne, FractionalIdeal.coeIdeal_eq_zero]; exact ha),
      ih ha, mul_add]
    congr 1

    let qv : HeightOneSpectrum R := ⟨q, Ideal.isPrime_of_prime hq, hq0⟩
    have h1 := count_map_prime (R := R) KT qv P
    rw [show ((q.map (algebraMap R T) : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) =
        ((qv.asIdeal.map (algebraMap R T) : Ideal T) : FractionalIdeal (nonZeroDivisors T) KT) from rfl, h1,
      show ((q : Ideal R) : FractionalIdeal (nonZeroDivisors R) KR) = ((qv.asIdeal : Ideal R) : FractionalIdeal (nonZeroDivisors R) KR) from rfl]
    by_cases hPq : P.asIdeal.under R = qv.asIdeal
    · rw [if_pos hPq]
      have : underv (R := R) P = qv := HeightOneSpectrum.ext hPq
      rw [this, FractionalIdeal.count_self, mul_one]
      rw [hPq]
    · rw [if_neg hPq]
      have hne : qv ≠ underv (R := R) P := fun h => hPq (by rw [h]; rfl)
      rw [FractionalIdeal.count_maximal_coprime KR (underv (R := R) P) hne, mul_zero]

end L4
end CapInj

namespace CapInj

section L3b
variable (F : Type) [Field F] [NumberField F] (S : Set Nat.Primes)

lemma mk_mem_closure_of_sSupported (I : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ placesOverPrimes F S → FractionalIdeal.count F w (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0) :
    ClassGroup.mk F I ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S) := by
  have hfac := FractionalIdeal.finprod_heightOneSpectrum_factorization' F I.ne_zero

  have key : ∃ u : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ,
      (u : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = ∏ᶠ (v : HeightOneSpectrum (𝓞 F)), (v.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ^ FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) ∧
      ClassGroup.mk F u ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S) := by
    refine finprod_induction (fun M => ∃ u : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ, (u : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = M ∧
        ClassGroup.mk F u ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S)) ⟨1, Units.val_one, ?_⟩ ?_ ?_
    · rw [map_one]; exact Subgroup.one_mem _
    · rintro M N ⟨u, rfl, hu⟩ ⟨u', rfl, hu'⟩
      exact ⟨u * u', Units.val_mul _ _, by rw [map_mul]; exact Subgroup.mul_mem _ hu hu'⟩
    · intro v
      by_cases hv : FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) = 0
      · refine ⟨1, by rw [hv, zpow_zero, Units.val_one], by rw [map_one]; exact Subgroup.one_mem _⟩
      · have hvS : v ∈ placesOverPrimes F S := by by_contra hvS; exact hv (h v hvS)
        let u₀ : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ :=
          FractionalIdeal.mk0 F ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 (by simpa using v.ne_bot)⟩
        refine ⟨u₀ ^ FractionalIdeal.count F v (I : FractionalIdeal (nonZeroDivisors (𝓞 F)) F), ?_, ?_⟩
        · rw [Units.val_zpow_eq_zpow_val]; rfl
        · have hu₀ : ClassGroup.mk F u₀ = primeClass F v := by rw [ClassGroup.mk_mk0]; rfl
          rw [map_zpow, hu₀]
          exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem _ hvS)) _
  obtain ⟨u, hu, hmem⟩ := key
  have : u = I := Units.ext (hu.trans hfac)
  rwa [this] at hmem

lemma exists_ideal_data (p : ℕ) (C : ClassGroup (𝓞 F)) (hC : C ^ p ∈ Subgroup.closure (primeClass F '' placesOverPrimes F S)) :
    ∃ (A : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ) (x : F), x ≠ 0 ∧ ClassGroup.mk F A = C⁻¹ ∧
      ∀ w : HeightOneSpectrum (𝓞 F), w ∉ placesOverPrimes F S →
        (p : ℤ) * FractionalIdeal.count F w (A : FractionalIdeal (nonZeroDivisors (𝓞 F)) F) =
          FractionalIdeal.count F w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 F)) x) := by
  obtain ⟨I₀, hI₀⟩ := ClassGroup.mk0_surjective C⁻¹
  obtain ⟨J, hJ, hJS⟩ := exists_sSupported_of_mem_closure F S _ hC
  let A : (FractionalIdeal (nonZeroDivisors (𝓞 F)) F)ˣ := FractionalIdeal.mk0 F I₀
  have hA : ClassGroup.mk F A = C⁻¹ := by rw [ClassGroup.mk_mk0]; exact hI₀
  have h1 : ClassGroup.mk F (A ^ p * J) = 1 := by rw [map_mul, map_pow, hA, hJ, inv_pow, inv_mul_cancel]
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  refine ⟨A, x, fun hx0 => ?_, hA, fun w hw => ?_⟩
  · rw [hx0, FractionalIdeal.spanSingleton_zero] at hx
    exact (A ^ p * J).ne_zero hx
  · rw [← hx, Units.val_mul, Units.val_pow_eq_pow_val, FractionalIdeal.count_mul F w (pow_ne_zero _ A.ne_zero) J.ne_zero,
      FractionalIdeal.count_pow, hJS w hw, add_zero]

end L3b
end CapInj

namespace CycBaseCAP

section injProof

open IsDedekindDomain NumberField

variable (S : Finset Nat.Primes) (L F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F)
  [FiniteDimensional ℚ ↥L] [FiniteDimensional ℚ ↥F]

lemma natCast_mem_unique' {K : Type} [Field K] [NumberField K] {q q' : ℕ} (hq : q.Prime) (hq' : q'.Prime)
    (w : HeightOneSpectrum (𝓞 K)) (h : ((q : 𝓞 K)) ∈ w.asIdeal) (h' : ((q' : 𝓞 K)) ∈ w.asIdeal) : q = q' := by
  by_contra hne
  have hcop : IsCoprime ((q : 𝓞 K)) ((q' : 𝓞 K)) := by
    have := (Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hq hq').2 hne)).map (Int.castRingHom (𝓞 K))
    simpa using this
  obtain ⟨a, b, hab⟩ := hcop
  apply w.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← hab]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ h')

lemma inv_natCast_not_mem' {q : ℕ} (hq : q.Prime) {A : ValuationSubring (AlgebraicClosure ℚ)} (hA : A.LiesOverPrime q) :
    ((q : AlgebraicClosure ℚ))⁻¹ ∉ A := by
  intro h
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hq.ne_zero
  have h1 : A.valuation ((q : AlgebraicClosure ℚ))⁻¹ ≤ 1 := (A.valuation_le_one_iff _).2 h
  have h2 : A.valuation (q : AlgebraicClosure ℚ) < 1 := (ValuationSubring.mem_nonunits_iff A).1 hA
  rw [map_inv₀, inv_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hq0))] at h1
  exact absurd h2 (not_lt.2 h1)

lemma valuation_algebraMap_eq [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S) (v' : HeightOneSpectrum (𝓞 ↥F))
    (hv'S : ∀ q : Nat.Primes, q ∈ S → ((q : ℕ) : 𝓞 ↥F) ∉ v'.asIdeal) (z : ↥L) (hz : z ≠ 0) :
    letI := algLF L F hLF
    haveI := isIntegral_OLF L F hLF
    v'.valuation ↥F (algebraMap ↥L ↥F z) = (CapInj.underv (R := 𝓞 ↥L) v').valuation ↥L z := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  haveI := isIntegral_OLF L F hLF
  haveI := faithfulSMul_OLF L F hLF
  have he : (v'.asIdeal.under (𝓞 ↥L)).ramificationIdx' v'.asIdeal = 1 :=
    ramificationIdx_eq_one' S L F hLF hF v'.asIdeal v'.isMaximal hv'S

  have key : ∀ r : 𝓞 ↥L, r ≠ 0 →
      v'.valuation ↥F (algebraMap (𝓞 ↥F) ↥F (algebraMap (𝓞 ↥L) (𝓞 ↥F) r)) = (CapInj.underv (R := 𝓞 ↥L) v').valuation ↥L (algebraMap (𝓞 ↥L) ↥L r) := by
    intro r hr
    have hr' : algebraMap (𝓞 ↥L) (𝓞 ↥F) r ≠ 0 := (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).2 hr
    rw [CapInj.valuation_eq_exp_neg_count ↥F v' _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr')),
      CapInj.valuation_eq_exp_neg_count ↥L _ _ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (mem_nonZeroDivisors_of_ne_zero hr)),
      ← FractionalIdeal.coeIdeal_span_singleton, ← FractionalIdeal.coeIdeal_span_singleton,
      show (Ideal.span {algebraMap (𝓞 ↥L) (𝓞 ↥F) r} : Ideal (𝓞 ↥F)) = (Ideal.span {r}).map (algebraMap (𝓞 ↥L) (𝓞 ↥F)) by
        rw [Ideal.map_span, Set.image_singleton],
      CapInj.count_map ↥L ↥F v' (Ideal.span {r}) (by rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]; exact hr), he, Nat.cast_one, one_mul]
  obtain ⟨r, s, hs, hzrs⟩ := IsFractionRing.div_surjective (A := 𝓞 ↥L) z
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hzrs
    exact hz hzrs.symm
  rw [← hzrs, map_div₀, map_div₀, map_div₀, ← key r hr0, ← key s hs0]
  congr 1 <;> congr 1 <;> exact (IsScalarTower.algebraMap_apply (𝓞 ↥L) (𝓞 ↥F) ↥F _).symm.trans (IsScalarTower.algebraMap_apply (𝓞 ↥L) ↥L ↥F _)

theorem exists_div_sunit_of_classOf_eq_zero' [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S) (α : (↥F)ˣ)
    (hα : ∀ g : ↥L.fixingSubgroup, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ) ∈ A ∧
      (((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ)) / ((α : ↥F) : AlgebraicClosure ℚ))⁻¹ ∈ A)
    (h0 : idealOf L F hLF α ≠ 0)
    (hcls : (Submodule.Quotient.mk (Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 (idealOf L F hLF α) h0))) :
      sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0) :
    ∃ β : (↥L)ˣ, ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      ((α : ↥F) : AlgebraicClosure ℚ) / ((β : ↥L) : AlgebraicClosure ℚ) ∈ A ∧
        (((α : ↥F) : AlgebraicClosure ℚ) / ((β : ↥L) : AlgebraicClosure ℚ))⁻¹ ∈ A := by
  letI := algLF L F hLF
  haveI := isScalarTower_LF L F hLF
  haveI := isScalarTower_LFQ L F hLF
  haveI := isIntegral_OLF L F hLF

  have hc : ClassGroup.mk ↥L (Units.mk0 (idealOf L F hLF α) h0) ∈ Subgroup.closure (primeClass ↥L '' placesOverPrimes ↥L (S : Set Nat.Primes)) := by
    rw [← NumberField.LevelArith.sPrimeClasses_eq_closure ↥L ↥L]
    exact (Submodule.Quotient.mk_eq_zero _).1 hcls
  obtain ⟨I, hI, hIS⟩ := CapInj.exists_sSupported_of_mem_closure ↥L (S : Set Nat.Primes) _ hc
  obtain ⟨x, hx0, hx⟩ := CapInj.exists_eq_spanSingleton_mul_of_mk_eq ↥L (Units.mk0 (idealOf L F hLF α) h0) I hI.symm
  rw [Units.val_mk0] at hx
  refine ⟨(Units.mk0 x hx0)⁻¹, fun q hq A hA => ?_⟩

  have hAF : ∃ y : ↥F, algebraMap ↥F (AlgebraicClosure ℚ) y ∉ A :=
    ⟨(((q : Nat.Primes) : ℕ) : ↥F)⁻¹, by rw [map_inv₀, map_natCast]; exact inv_natCast_not_mem' (q : Nat.Primes).2 hA⟩
  obtain ⟨v', hv'⟩ := (NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one ↥F
    (algebraMap ↥F (AlgebraicClosure ℚ)) A hAF).exists
  have hq0F : (((q : Nat.Primes) : ℕ) : ↥F) ≠ 0 := Nat.cast_ne_zero.2 (q : Nat.Primes).2.ne_zero
  have hvq : v'.valuation ↥F (((q : Nat.Primes) : ℕ) : ↥F) < 1 := by
    by_contra hge
    rw [not_lt] at hge
    have hle : v'.valuation ↥F (((q : Nat.Primes) : ℕ) : ↥F) ≤ 1 := (hv' _).1 (by rw [map_natCast]; exact natCast_mem A _)
    have heq : v'.valuation ↥F (((q : Nat.Primes) : ℕ) : ↥F) = 1 := le_antisymm hle hge
    have hmem : algebraMap ↥F (AlgebraicClosure ℚ) ((((q : Nat.Primes) : ℕ) : ↥F))⁻¹ ∈ A := (hv' _).2 (by rw [map_inv₀, heq, inv_one])
    rw [map_inv₀, map_natCast] at hmem
    exact inv_natCast_not_mem' (q : Nat.Primes).2 hA hmem
  have hqv' : (((q : Nat.Primes) : ℕ) : 𝓞 ↥F) ∈ v'.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := ↥F)]
    rw [show (((q : Nat.Primes) : ℕ) : ↥F) = algebraMap (𝓞 ↥F) ↥F (((q : Nat.Primes) : ℕ) : 𝓞 ↥F) from (map_natCast _ _).symm] at hvq
    exact hvq
  have hv'S : ∀ q' : Nat.Primes, q' ∈ S → ((q' : ℕ) : 𝓞 ↥F) ∉ v'.asIdeal := fun q' hq'S h =>
    hq ((show q = q' from Subtype.ext (natCast_mem_unique' (q : Nat.Primes).2 (q' : Nat.Primes).2 v' hqv' h)) ▸ hq'S)
  have hwPOP : CapInj.underv (R := 𝓞 ↥L) v' ∉ placesOverPrimes ↥L (S : Set Nat.Primes) := by
    rintro ⟨q', hq'S, hq'w⟩
    apply hv'S q' hq'S
    rw [CapInj.underv_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hq'w
    exact hq'w

  obtain ⟨-, hcount⟩ := idealOf_spec' S L F hLF α hα
  have hcw := hcount (CapInj.underv (R := 𝓞 ↥L) v') hwPOP v' rfl
  have hsx0 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) x ≠ (0 : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) := by
    rw [Ne, FractionalIdeal.spanSingleton_eq_zero_iff]; exact hx0
  have hcx : FractionalIdeal.count ↥L (CapInj.underv (R := 𝓞 ↥L) v') (idealOf L F hLF α) =
      FractionalIdeal.count ↥L (CapInj.underv (R := 𝓞 ↥L) v') (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) x) := by
    rw [hx, FractionalIdeal.count_mul ↥L _ hsx0 I.ne_zero, hIS _ hwPOP, add_zero]

  have hvα : v'.valuation ↥F (α : ↥F) =
      WithZero.exp (FractionalIdeal.count ↥L (CapInj.underv (R := 𝓞 ↥L) v') (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) x)) := by
    rw [← hcx, hcw, ← HeightOneSpectrum.valuationOfNeZero_eq]
    show ((v'.valuationOfNeZero α : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      ((Multiplicative.ofAdd (Multiplicative.toAdd (v'.valuationOfNeZero α)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [ofAdd_toAdd]
  have hvβ : v'.valuation ↥F (algebraMap ↥L ↥F x⁻¹) =
      WithZero.exp (FractionalIdeal.count ↥L (CapInj.underv (R := 𝓞 ↥L) v') (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥L)) x)) := by
    rw [valuation_algebraMap_eq S L F hLF hF v' hv'S x⁻¹ (inv_ne_zero hx0), map_inv₀, CapInj.valuation_eq_exp_neg_count ↥L _ x hx0,
      ← WithZero.exp_neg, neg_neg]
  have hxF0 : algebraMap ↥L ↥F x⁻¹ ≠ 0 := by
    rw [map_inv₀]; exact inv_ne_zero ((map_ne_zero_iff _ (algebraMap ↥L ↥F).injective).2 hx0)
  have hαβ0 : (α : ↥F) / algebraMap ↥L ↥F x⁻¹ ≠ 0 := div_ne_zero α.ne_zero hxF0
  have hunit := (unit_iff_valuation_eq_one F A v' (fun y => hv' y) ((α : ↥F) / algebraMap ↥L ↥F x⁻¹) hαβ0).2
    (by rw [map_div₀, hvα, hvβ, div_self (WithZero.exp_ne_zero)])

  have hcoe : ((((Units.mk0 x hx0)⁻¹ : (↥L)ˣ) : ↥L) : AlgebraicClosure ℚ) = ((algebraMap ↥L ↥F x⁻¹ : ↥F) : AlgebraicClosure ℚ) := by
    rw [Units.val_inv_eq_inv_val, Units.val_mk0]; rfl
  have hdiv : ((α : ↥F) : AlgebraicClosure ℚ) / ((algebraMap ↥L ↥F x⁻¹ : ↥F) : AlgebraicClosure ℚ) =
      (((α : ↥F) / algebraMap ↥L ↥F x⁻¹ : ↥F) : AlgebraicClosure ℚ) := by push_cast; rfl
  rw [hcoe, hdiv]
  exact hunit

end injProof

end CycBaseCAP

end

private local instance _root_.CapTors.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
p2m_export "" "CapTors.isAlgebraicQbar"
private local instance _root_.CapTors.isAlgClosureQbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
p2m_export "" "CapTors.isAlgClosureQbar"
private local instance _root_.CapTors.normalQbar : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)

p2m_export "" "CapTors.normalQbar"
namespace CycBaseCAP

section torsProof

open IsDedekindDomain NumberField

lemma toAdd_valuationOfNeZero_eq_neg_count (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥K]
    (w : HeightOneSpectrum (𝓞 ↥K)) (x : ↥K) (hx : x ≠ 0) :
    Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 x hx)) =
      -FractionalIdeal.count ↥K w (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 ↥K)) x) := by
  have h := HeightOneSpectrum.valuationOfNeZero_eq w (Units.mk0 x hx)
  rw [Units.val_mk0, CapInj.valuation_eq_exp_neg_count ↥K w x hx, WithZero.exp] at h
  have h' := WithZero.coe_injective h
  rw [h', toAdd_ofAdd]

lemma exists_kummer_level {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (x : ↥L) (hx : x ≠ 0)
    (hdiv : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
      (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 x hx)))
    (y : AlgebraicClosure ℚ) (hy : y ^ p = (x : AlgebraicClosure ℚ)) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), L ≤ F ∧ y ∈ F ∧ F.IsUnramifiedOutside S ∧ IsGalois ℚ ↥F ∧ FiniteDimensional ℚ ↥F := by

  have hyint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  haveI : FiniteDimensional ℚ ↥(IntermediateField.adjoin ℚ {y}) := IntermediateField.adjoin.finiteDimensional hyint
  let E₀ : IntermediateField ℚ (AlgebraicClosure ℚ) := L ⊔ IntermediateField.adjoin ℚ {y}
  haveI hE₀fd : FiniteDimensional ℚ ↥E₀ := IntermediateField.finiteDimensional_sup L _

  have hE₀ : E₀.IsUnramifiedOutside S := by
    refine ⟨hE₀fd, fun q hq A hA σ hσ => ?_⟩
    have hσL : σ ∈ L.fixingSubgroup := hL.2 q hq A hA hσ
    rw [IntermediateField.fixingSubgroup_sup]
    refine ⟨hσL, ?_⟩

    have hAF : ∃ z : ↥L, algebraMap ↥L (AlgebraicClosure ℚ) z ∉ A :=
      ⟨(((q : Nat.Primes) : ℕ) : ↥L)⁻¹, by rw [map_inv₀, map_natCast]; exact inv_natCast_not_mem' (q : Nat.Primes).2 hA⟩
    obtain ⟨w, hw⟩ := (NumberField.existsUnique_heightOneSpectrum_forall_map_mem_iff_valuation_le_one ↥L
      (algebraMap ↥L (AlgebraicClosure ℚ)) A hAF).exists
    have hvq : w.valuation ↥L (((q : Nat.Primes) : ℕ) : ↥L) < 1 := by
      by_contra hge
      rw [not_lt] at hge
      have hle : w.valuation ↥L (((q : Nat.Primes) : ℕ) : ↥L) ≤ 1 := (hw _).1 (by rw [map_natCast]; exact natCast_mem A _)
      have heq : w.valuation ↥L (((q : Nat.Primes) : ℕ) : ↥L) = 1 := le_antisymm hle hge
      have hmem : algebraMap ↥L (AlgebraicClosure ℚ) ((((q : Nat.Primes) : ℕ) : ↥L))⁻¹ ∈ A := (hw _).2 (by rw [map_inv₀, heq, inv_one])
      rw [map_inv₀, map_natCast] at hmem
      exact inv_natCast_not_mem' (q : Nat.Primes).2 hA hmem
    have hqw : (((q : Nat.Primes) : ℕ) : 𝓞 ↥L) ∈ w.asIdeal := by
      rw [← HeightOneSpectrum.intValuation_lt_one_iff_mem, ← HeightOneSpectrum.valuation_of_algebraMap (K := ↥L)]
      rw [show (((q : Nat.Primes) : ℕ) : ↥L) = algebraMap (𝓞 ↥L) ↥L (((q : Nat.Primes) : ℕ) : 𝓞 ↥L) from (map_natCast _ _).symm] at hvq
      exact hvq
    have hwS : w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) := by
      rintro ⟨q', hq'S, hq'w⟩
      exact hq ((show q = q' from Subtype.ext (natCast_mem_unique' (q : Nat.Primes).2 (q' : Nat.Primes).2 w hqw hq'w)) ▸ hq'S)
    have hqp : ((q : Nat.Primes) : ℕ) ≠ p := fun h => hq (by
      have : q = pPrime p := Subtype.ext h
      rw [this]; exact hpS)
    have hσy : σ y = y :=
      NumberField.LevelArith.inertia_apply_eq_of_dvd_valuation p L (Units.mk0 x hx) w ((q : Nat.Primes) : ℕ) (q : Nat.Primes).2 hqp hqw
        (hdiv w hwS) y (by rw [Units.val_mk0]; exact hy) A (fun z => hw z) σ hσ
        (fun z => (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσL _ z.2)
    show σ ∈ (IntermediateField.adjoin ℚ {y}).fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro z hz
    induction hz using IntermediateField.adjoin_induction with
    | mem t ht => rw [Set.mem_singleton_iff] at ht; subst ht; exact hσy
    | algebraMap r => exact AlgEquiv.commutes σ r
    | add a b _ _ ha hb => rw [map_add, ha, hb]
    | inv a _ ha => rw [map_inv₀, ha]
    | mul a b _ _ ha hb => rw [map_mul, ha, hb]

  have hyE₀ : y ∈ E₀ := (le_sup_right : IntermediateField.adjoin ℚ {y} ≤ E₀) (IntermediateField.subset_adjoin ℚ {y} (Set.mem_singleton y))
  haveI : Normal ℚ ↥(IntermediateField.normalClosure ℚ (↥E₀) (AlgebraicClosure ℚ)) := normalClosure.normal ℚ (↥E₀) (AlgebraicClosure ℚ)
  exact ⟨IntermediateField.normalClosure ℚ (↥E₀) (AlgebraicClosure ℚ), le_sup_left.trans (IntermediateField.le_normalClosure E₀),
    IntermediateField.le_normalClosure E₀ hyE₀, IntermediateField.IsUnramifiedOutside.normalClosure hE₀, ⟨⟩, inferInstance⟩

end torsProof
end CycBaseCAP

namespace CycBaseCAP
section torsProof2
open IsDedekindDomain NumberField

theorem exists_kummer_level_of_torsion' {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]
    (C : ClassGroup (𝓞 ↥L))
    (hC : p • (Submodule.Quotient.mk (Additive.ofMul C) : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0) :
    ∃ (F : IntermediateField ℚ (AlgebraicClosure ℚ)) (hLF : L ≤ F) (_ : F.IsUnramifiedOutside S) (_ : IsGalois ℚ ↥F)
      (_ : FiniteDimensional ℚ ↥F) (α : (↥F)ˣ),
      ((α : ↥F) : AlgebraicClosure ℚ) ^ p ∈ L ∧
      (∀ g : ↥L.fixingSubgroup, ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) / ((α : ↥F) : AlgebraicClosure ℚ)) ^ p = 1) ∧
      ∃ h0 : idealOf L F hLF α ≠ 0,
        (Submodule.Quotient.mk (Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 (idealOf L F hLF α) h0))) :
          sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = Submodule.Quotient.mk (Additive.ofMul C) := by
  have hp : p.Prime := Fact.out
  have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hp.ne_zero

  have hCp : C ^ p ∈ Subgroup.closure (primeClass ↥L '' placesOverPrimes ↥L (S : Set Nat.Primes)) := by
    rw [← NumberField.LevelArith.sPrimeClasses_eq_closure ↥L ↥L]
    have h1 : (Submodule.Quotient.mk (Additive.ofMul (C ^ p)) : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0 := by
      show (Submodule.mkQ (sPrimeClassesSubmodule ↥L ↥L (S : Set Nat.Primes))) (p • Additive.ofMul C) = 0
      rw [map_nsmul]
      exact hC
    exact (Submodule.Quotient.mk_eq_zero _).1 h1

  obtain ⟨𝔞, x, hx0, h𝔞, hcnt⟩ := CapInj.exists_ideal_data ↥L (S : Set Nat.Primes) p C hCp

  have hdiv : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
      (p : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.mk0 x hx0)) := fun w hw =>
    ⟨-FractionalIdeal.count ↥L w (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L), by
      rw [toAdd_valuationOfNeZero_eq_neg_count L w x hx0, ← hcnt w hw, mul_neg]⟩

  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq ((x : ↥L) : AlgebraicClosure ℚ) hp.pos
  obtain ⟨F, hLF, hyF, hF, hGal, hFD⟩ := exists_kummer_level S hpS L hL x hx0 hdiv y hy
  haveI := hGal
  haveI := hFD
  have hx0' : ((x : ↥L) : AlgebraicClosure ℚ) ≠ 0 := fun h => hx0 (Subtype.ext h)
  have hy0 : y ≠ 0 := by rintro rfl; rw [zero_pow hp.ne_zero] at hy; exact hx0' hy.symm
  let α : (↥F)ˣ := Units.mk0 ⟨y, hyF⟩ (fun h => hy0 (congrArg Subtype.val h))
  have hαy : ((α : ↥F) : AlgebraicClosure ℚ) = y := rfl
  refine ⟨F, hLF, hF, hGal, hFD, α, ?_, ?_, ?_⟩
  · rw [hαy, hy]; exact x.2
  · intro g
    have hgx : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((x : ↥L) : AlgebraicClosure ℚ) = ((x : ↥L) : AlgebraicClosure ℚ) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ x.2
    rw [hαy, div_pow, ← map_pow, hy, hgx, div_self hx0']
  ·
    letI := algLF L F hLF
    haveI := isScalarTower_LF L F hLF
    refine ⟨idealOf_ne_zero' L F hLF α, ?_⟩

    have hval : ∀ w : HeightOneSpectrum (𝓞 ↥L), w ∉ placesOverPrimes ↥L (S : Set Nat.Primes) →
        expo L F hLF α w = -FractionalIdeal.count ↥L w (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L) := by
      intro w hw
      have hunder := primeOver_under L F hLF w
      have hw'S := not_mem_placesOverPrimes_of_under S L F hLF w hw (primeOver L F hLF w) hunder
      have he : Ideal.ramificationIdx' w.asIdeal (primeOver L F hLF w).asIdeal = 1 := by
        have := ramificationIdx_eq_one' S L F hLF hF (primeOver L F hLF w).asIdeal (primeOver L F hLF w).isMaximal
          (fun q hq h => hw'S ⟨q, hq, h⟩)
        rwa [hunder] at this
      have hαp : (α : ↥F) ^ p = algebraMap ↥L ↥F x := by
        apply Subtype.ext
        rw [show (((α : ↥F) ^ p : ↥F) : AlgebraicClosure ℚ) = ((α : ↥F) : AlgebraicClosure ℚ) ^ p by push_cast; rfl, hαy, hy]
        rfl
      have h1 : ((primeOver L F hLF w).valuation ↥F (α : ↥F)) ^ p = w.valuation ↥L x := by
        rw [← map_pow, hαp, valuation_algebraMap_eq_of_ramificationIdx_eq_one' L F hLF w (primeOver L F hLF w) hunder he x]
      have h2 : (primeOver L F hLF w).valuationOfNeZero α ^ p =
          Multiplicative.ofAdd (-((p : ℤ) * FractionalIdeal.count ↥L w (𝔞 : FractionalIdeal (nonZeroDivisors (𝓞 ↥L)) ↥L))) := by
        apply WithZero.coe_injective
        rw [WithZero.coe_pow, HeightOneSpectrum.valuationOfNeZero_eq, h1, CapInj.valuation_eq_exp_neg_count ↥L w x hx0, ← hcnt w hw]
        rfl
      have h3 := congrArg Multiplicative.toAdd h2
      rw [toAdd_pow, toAdd_ofAdd, nsmul_eq_mul, ← mul_neg] at h3
      unfold expo
      exact mul_left_cancel₀ hp0 h3

    apply (Submodule.Quotient.eq _).2
    change Additive.toMul (Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 (idealOf L F hLF α) (idealOf_ne_zero' L F hLF α))) - Additive.ofMul C) ∈
      sPrimeClasses ↥L ↥L (S : Set Nat.Primes)
    rw [toMul_sub, toMul_ofMul, toMul_ofMul, div_eq_mul_inv, NumberField.LevelArith.sPrimeClasses_eq_closure, ← h𝔞, ← map_mul]
    apply CapInj.mk_mem_closure_of_sSupported ↥L (S : Set Nat.Primes)
    intro w hw
    rw [Units.val_mul, Units.val_mk0, FractionalIdeal.count_mul ↥L w (idealOf_ne_zero' L F hLF α) 𝔞.ne_zero]
    unfold idealOf
    rw [FractionalIdeal.count_finprod ↥L w _ (expo_eventually_eq_zero L F hLF α), hval w hw, neg_add_cancel]

end torsProof2

section asm5

open IsDedekindDomain NumberField groupCohomology

variable (S : Finset Nat.Primes) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

lemma mem_sUnitsMaxStable_of_unit {F : IntermediateField ℚ (AlgebraicClosure ℚ)} (hF : F.IsUnramifiedOutside S)
    (ε : (AlgebraicClosure ℚ)ˣ) (hεF : (ε : AlgebraicClosure ℚ) ∈ F)
    (hunit : ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      (ε : AlgebraicClosure ℚ) ∈ A ∧ ((ε : AlgebraicClosure ℚ))⁻¹ ∈ A) : ε ∈ sUnitsMaxStable S L := by
  rw [NumberField.LevelArith.sUnitsMaxStable_eq_sUnitsMax]
  refine ⟨⟨F, hF, hεF⟩, fun q hq A hA => ?_⟩
  obtain ⟨h1, h2⟩ := hunit q hq A hA
  rw [Units.val_inv_eq_inv_val]; exact ⟨h1, h2⟩

set_option maxHeartbeats 6400000 in

theorem fX_injective (hL : L.IsUnramifiedOutside S) : Function.Injective (fX S L hL) := by
  intro x y hxy
  rw [← sub_eq_zero] at hxy ⊢
  rw [← map_sub] at hxy
  set z := x - y with hz

  let c := CycBaseLES.rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) z
  let d := datum₀ hL c
  haveI : FiniteDimensional ℚ ↥d.F := d.hF.1
  haveI := d.gal
  have hcls : (Submodule.Quotient.mk (Additive.ofMul (ClassGroup.mk ↥L (Units.mk0 (idealOf L d.F d.hLF d.α) (idealOf_ne_zero' L d.F d.hLF d.α)))) :
      sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0 := hxy
  obtain ⟨β, hβ⟩ := exists_div_sunit_of_classOf_eq_zero' S L d.F d.hLF d.hF d.α d.hα (idealOf_ne_zero' L d.F d.hLF d.α) hcls

  have hα0 : ((d.α : ↥d.F) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => d.α.ne_zero (Subtype.ext h0)
  have hβ0 : ((β : ↥L) : AlgebraicClosure ℚ) ≠ 0 := fun h0 => β.ne_zero (Subtype.ext h0)
  let ε : (AlgebraicClosure ℚ)ˣ := Units.mk0 (((d.α : ↥d.F) : AlgebraicClosure ℚ) / ((β : ↥L) : AlgebraicClosure ℚ)) (div_ne_zero hα0 hβ0)
  have hεF : (ε : AlgebraicClosure ℚ) ∈ d.F := div_mem (d.α : ↥d.F).2 (d.hLF (β : ↥L).2)
  have hεmem : ε ∈ sUnitsMaxStable S L := mem_sUnitsMaxStable_of_unit S L d.hF ε hεF hβ
  let e₁ : sUnitsMaxRep S L := ⟨Additive.ofMul ε, hεmem⟩

  have hcob : ∀ g : ↥L.fixingSubgroup, c.1 g = (d₀₁ (sUnitsMaxRep S L)).hom e₁ g := by
    intro g
    rw [d₀₁_hom_apply]
    apply Subtype.ext
    apply Additive.toMul.injective
    apply Units.ext
    show ((sUnitsMaxRep.val S L (c.1 g) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      (((sUnitsMaxRep.val S L ((sUnitsMaxRep S L).ρ g e₁) / sUnitsMaxRep.val S L e₁ : (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ)
    rw [d.hcob g, Units.val_div_eq_div_val, sUnitsMaxRep.val_ρ]
    have hgβ : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((β : ↥L) : AlgebraicClosure ℚ) = ((β : ↥L) : AlgebraicClosure ℚ) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 g.2 _ (β : ↥L).2
    show _ = (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (((d.α : ↥d.F) : AlgebraicClosure ℚ) / ((β : ↥L) : AlgebraicClosure ℚ)) /
      (((d.α : ↥d.F) : AlgebraicClosure ℚ) / ((β : ↥L) : AlgebraicClosure ℚ))
    rw [map_div₀, hgβ]
    field_simp
  have hmem : (c.1 : ↥L.fixingSubgroup → sUnitsMaxRep S L) ∈ coboundaries₁ (sUnitsMaxRep S L) :=
    LinearMap.mem_range.mpr ⟨e₁, (funext hcob).symm⟩
  have h1 : (H1π (sUnitsMaxRep S L)).hom c.1 = 0 := (H1π_eq_zero_iff c.1).mpr hmem
  apply Subtype.ext
  show z.1 = 0
  rw [← CycBaseLES.H1π_rep L.fixingSubgroup.subtype S (sUnitsMaxRep S L) z]
  exact h1

end asm5

section asm6

open IsDedekindDomain NumberField groupCohomology

private local instance _root_.CycBaseCAP.Asm6.isAlgebraicQbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

p2m_export "CycBaseCAP" "Asm6.isAlgebraicQbar"
variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ ↥L]

include hpS in

lemma mem_sUnitsMaxStable_of_pow_eq_one (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) ^ p = 1) : u ∈ sUnitsMaxStable S L := by
  have hp : p.Prime := Fact.out
  rw [NumberField.LevelArith.sUnitsMaxStable_eq_sUnitsMax]
  have hlev : (⊥ ⊔ IntermediateField.adjoin ℚ {(u : AlgebraicClosure ℚ)}).IsUnramifiedOutside S :=
    IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq S (pPrime p) hpS ⊥ (IntermediateField.isUnramifiedOutside_bot S)
      1 (one_mem _) (fun q _ A _ => ⟨one_mem A, by rw [inv_one]; exact one_mem A⟩) (u : AlgebraicClosure ℚ) hu
  refine ⟨⟨_, hlev, (le_sup_right : IntermediateField.adjoin ℚ {(u : AlgebraicClosure ℚ)} ≤ _) (IntermediateField.mem_adjoin_simple_self ℚ _)⟩,
    fun q _ A _ => ?_⟩
  have hv : A.valuation (u : AlgebraicClosure ℚ) = 1 := by
    have h := congrArg A.valuation hu
    rw [map_pow, map_one] at h
    exact (pow_eq_one_iff_left hp.ne_zero).mp h
  refine ⟨(A.valuation_le_one_iff _).mp hv.le, ?_⟩
  rw [Units.val_inv_eq_inv_val]
  exact (A.valuation_le_one_iff _).mp (by rw [map_inv₀, hv, inv_one])

include hpS in
set_option maxHeartbeats 6400000 in

theorem exists_torsion_preimage (hL : L.IsUnramifiedOutside S) (C : ClassGroup (𝓞 ↥L))
    (hC : p • (Submodule.Quotient.mk (Additive.ofMul C) : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0) :
    ∃ x : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)), p • x = 0 ∧
      fX S L hL x = Submodule.Quotient.mk (Additive.ofMul C) := by
  have hp : p.Prime := Fact.out
  obtain ⟨F, hLF, hF, hgal, hFD, α, hαp, hroot, h0, hcls⟩ := exists_kummer_level_of_torsion' S hpS L hL C hC
  haveI := hgal; haveI := hFD
  have hα0 : ((α : ↥F) : AlgebraicClosure ℚ) ≠ 0 := fun h => α.ne_zero (Subtype.ext h)

  let u : ↥L.fixingSubgroup → (AlgebraicClosure ℚ)ˣ := fun g =>
    Units.mk0 ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) / ((α : ↥F) : AlgebraicClosure ℚ))
      (div_ne_zero ((map_ne_zero _).mpr hα0) hα0)
  have hu : ∀ g, ((u g : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) / ((α : ↥F) : AlgebraicClosure ℚ) := fun g => rfl
  let cfun : ↥L.fixingSubgroup → sUnitsMaxRep S L := fun g =>
    ⟨Additive.ofMul (u g), mem_sUnitsMaxStable_of_pow_eq_one S hpS L (u g) (hroot g)⟩
  have hval : ∀ g, sUnitsMaxRep.val S L (cfun g) = u g := fun g => rfl
  have hcoc : cfun ∈ cocycles₁ (sUnitsMaxRep S L) := by
    rw [mem_cocycles₁_iff]
    intro g h
    apply Subtype.ext; apply Additive.toMul.injective; apply Units.ext
    show ((u (g * h) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      (((((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) • u h) * u g : (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ)
    rw [Units.val_mul, hu, hu]
    show ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) _ / _ =
      (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) _ / _) * _
    rw [AlgEquiv.mul_apply, map_div₀]
    have hgα : (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hα0
    field_simp
  have hlc : IsLevelConstantSr₁ L.fixingSubgroup.subtype S cfun := by
    refine ⟨F, hF, fun g s hs => ?_⟩
    apply Subtype.ext; apply Additive.toMul.injective; apply Units.ext
    show ((u (g * s) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = ((u g : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [hu, hu]
    show ((g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) * (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) _ / _ = _
    have hsα : (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ((α : ↥F) : AlgebraicClosure ℚ) = ((α : ↥F) : AlgebraicClosure ℚ) :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs _ (α : ↥F).2
    rw [AlgEquiv.mul_apply, hsα]
  let c : ↥(levelCocyclesSr₁ L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) := ⟨⟨cfun, hcoc⟩, hlc⟩
  let x : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) :=
    ⟨(H1π (sUnitsMaxRep S L)).hom c.1, H1π_mem_continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L) c.2⟩
  refine ⟨x, ?_, ?_⟩
  ·
    have hpc : p • c.1 = 0 := by
      apply Subtype.ext; funext g
      show p • cfun g = 0
      apply Subtype.ext; apply Additive.toMul.injective; apply Units.ext
      show (((u g) ^ p : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = 1
      rw [Units.val_pow_eq_pow_val]; exact hroot g
    apply Subtype.ext
    show p • (H1π (sUnitsMaxRep S L)).hom c.1 = 0
    rw [← map_nsmul, hpc, map_zero]
  ·
    let D : Datum c := ⟨F, hF, hgal, hLF, α, fun g => rfl⟩
    haveI : FiniteDimensional ℚ ↥D.F := hFD
    rw [show fX S L hL x = fXfun S L hL x from rfl, fXfun_eq S L hL x D rfl, D.cls_eq]
    exact hcls

end asm6

end CycBaseCAP

namespace CycBaseCAP

theorem mem_torsionBy_iff_of_subsingleton {M : Type} [AddCommGroup M] {I J : Module ℤ M} (a : ℤ) (x : M) :
    x ∈ @Submodule.torsionBy ℤ M _ _ I a ↔ x ∈ @Submodule.torsionBy ℤ M _ _ J a := by
  cases Subsingleton.elim I J; exact Iff.rfl

theorem torsionBy_heq_of_subsingleton {M : Type} [AddCommGroup M] {I J : Module ℤ M} (a : ℤ) :
    HEq (@Submodule.torsionBy ℤ M _ _ I a) (@Submodule.torsionBy ℤ M _ _ J a) := by
  cases Subsingleton.elim I J; exact HEq.rfl

section main

open groupCohomology

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S) (L : IntermediateField ℚ (AlgebraicClosure ℚ))
  (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L]

include hpS hL in

theorem key :
    ∃ f : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) →ₗ[ℤ] (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)),
      Function.Injective f ∧
        Submodule.map f (Submodule.torsionBy ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) =
          Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ) := by
  refine ⟨(fX S L hL).toIntLinearMap, fX_injective S L hL, ?_⟩
  ext C
  rw [Submodule.mem_map, Submodule.mem_torsionBy_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [Submodule.mem_torsionBy_iff] at hx
    show (p : ℤ) • fX S L hL x = 0
    rw [← map_zsmul, hx, map_zero]
  · intro hC
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ C
    have hC' : p • (Submodule.Quotient.mk (Additive.ofMul (Additive.toMul a)) : sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) = 0 := by
      rw [← natCast_zsmul]; exact hC
    obtain ⟨x, hpx, hfx⟩ := exists_torsion_preimage S hpS L hL (Additive.toMul a) hC'
    refine ⟨x, ?_, hfx⟩
    rw [Submodule.mem_torsionBy_iff, natCast_zsmul]
    exact hpx

end main

end CycBaseCAP

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) (hL : L.IsUnramifiedOutside S) [FiniteDimensional ℚ ↥L] :
    ∃ f : ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) →ₗ[ℤ] (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)),
      Function.Injective f ∧
        Submodule.map f (Submodule.torsionBy ℤ ↥(continuousH1Sr L.fixingSubgroup.subtype S (sUnitsMaxRep S L)) (p : ℤ)) =
          Submodule.torsionBy ℤ (sClassGroupRep ↥L ↥L (S : Set Nat.Primes)) (p : ℤ) := by
  have k := CycBaseCAP.key S hpS L hL
  first
  | exact k
  | (convert k using 5 <;>
      first
      | exact Subsingleton.elim _ _
      | exact CycBaseCAP.mem_torsionBy_iff_of_subsingleton _ _
      | (funext x; exact propext (CycBaseCAP.mem_torsionBy_iff_of_subsingleton _ _))
      | exact CycBaseCAP.torsionBy_heq_of_subsingleton _)

end S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective
end P2MW
export P2MW.S_NumberField_LevelArith_exists_continuousH1Sr_sUnitsMaxRep_linearMap_sClassGroupRep_injective (solution)
