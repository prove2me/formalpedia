-- Prove2me | solution 1 for GlobalTheory.VVRank.vvRank_of_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:00:08.997212+00:00
-- url     : https://prove2.me/submissions/17a419ca-aa44-4881-9850-35e651ccfff9

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ForallGeometricallyIntegralOfSmoothOfGeometrical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomFromSpecResidueField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatAndSurjectiveOfIsFiniteAbelianEnd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_MulAFiniteFlatSurjectiveEtale
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SpanEqTopOfFunctionals
import Theorems.Thm_GlobalTheory_VVRank_exists_gen_pullTo
import Theorems.Thm_GlobalTheory_VVRank_pullM_comp
import Theorems.Thm_GlobalTheory_VVRank_exists_isTwistPull
import Theorems.Thm_GlobalTheory_VVRank_exists_twist_pull
import Theorems.Thm_GlobalTheory_VVRank_exists_theta_pull
import Theorems.Thm_GlobalTheory_VVRank_mulT_comm
import Theorems.Thm_GlobalTheory_VVRank_inVV_of_isVVGen
import Theorems.Thm_GlobalTheory_VVRank_span_eq_top_of_functionals
import Theorems.Thm_GlobalTheory_VVRank_functional_mem_of_span
import Theorems.Thm_GlobalTheory_VVRank_exists_basis
import Theorems.Thm_GlobalTheory_VVRank_surjective_mulA
import Theorems.Thm_GlobalTheory_VVRank_surjective_mulT
import Theorems.Thm_GlobalTheory_VVRank_ofSec_eq_zero_of_twist
import Theorems.Thm_GlobalTheory_VVRank_comp_linComb
import Theorems.Thm_GlobalTheory_VVRank_linComb_pow
import Theorems.Thm_GlobalTheory_VVRank_span_translates_eq_top
import Theorems.Thm_GlobalTheory_VVRank_exists_geomPoint
import Theorems.Thm_GlobalTheory_VVRank_natCast_ne_zero
import Theorems.Thm_GlobalTheory_forall_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_isGen_genPull


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VVRank
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace
open scoped CategoryTheory.Obj
variable {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left}
namespace GlobalTheory.VVRank
theorem _root_.solution :
    SecBaseChangeAnySt → (∀ (S : Scheme.{0}) (P : PolAV S) (K : Type) [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S) (k : ℕ), (k = 1 ∨ 4 ≤ k) → (k : K) ≠ 0 → ∀ W : Submodule Γ((Over.mk t).left, ⊤) (SecM P.A P.L k (Over.mk t)), (∀ (θ : ThetaGrp P.A P.L k (Over.mk t)) (s s' : LB.Sec (LPow P.A P.L k (Over.mk t))), IsActOf P.A P.L k θ s s' → SecM.ofSec P.A s ∈ W → SecM.ofSec P.A s' ∈ W) → W = ⊥ ∨ W = ⊤) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), x ^ N = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ θ : ThetaGrp P.A P.L N (overRes V), θ.pt = overResι V ≫ x) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (N : ℕ) (T : Over S) (x : T ⟶ P.A), (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ ∃ c : LB.Gen ((thetaLB P.A P.L N x).pull ((fst T P.A).left ⁻¹ᵁ V).ι), c.IsGen) ↔ x ^ N = 1) → ∀ S : Scheme.{0}, VVRankSt (S := S) := by
  intro hbc hirr hmul hlift hact hker S P m ze hodd hunit hlev T p
  obtain ⟨lev⟩ := hlev
  have hcomm := P.isAb.comm
  have hm0 : m ≠ 0 := hodd.pos.ne'
  have hN : 1 ≤ m ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hm0)
  have hk : m ^ 2 = 1 ∨ 4 ≤ m ^ 2 := by
    rcases Nat.lt_or_ge m 2 with h | h
    · left; rw [show m = 1 by omega]; rfl
    · right; nlinarith
  have : NeZero (m ^ 2) := ⟨by omega⟩
  obtain ⟨V₀, hp₀, b₀, hb₀⟩ := hbc S P (m ^ 2) hN (T.hom p)
  obtain ⟨V₁, hp₁, b₁, hb₁⟩ := hbc S P 1 le_rfl (T.hom p)
  let toB : ∀ T : Over S, T ⟶ baseOver S := fun T => Over.homMk T.hom (Category.comp_id _)
  let x : (Fin (2 * P.g) → Fin (m ^ 2)) → (T ⟶ P.A) := fun c =>
    linComb (fun i => toB T ≫ lev.pt i) fun i => (c i : ℕ)
  have hx : ∀ c, x c ^ (m ^ 2) = 1 := fun c => linComb_pow _ _ _ fun i => by
    rw [← MonObj.comp_pow, lev.torsion, MonObj.comp_one]
  choose W hW U₀ hU₀ using fun c => hlift S P (m ^ 2) T (x c) (hx c) p
  obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := T.left.isBasis_affineOpens.exists_subset_of_mem_open
    (u := ((T.hom ⁻¹ᵁ V₀ : Set T.left) ∩ (T.hom ⁻¹ᵁ V₁ : Set T.left)) ∩ ⋂ c, (W c : Set T.left))
    ⟨⟨hp₀, hp₁⟩, Set.mem_iInter.2 hW⟩
    (((T.hom ⁻¹ᵁ V₀).isOpen.inter (T.hom ⁻¹ᵁ V₁).isOpen).inter
      (isOpen_iInter_of_finite fun c => (W c).isOpen))
  change T.left.Opens at V
  refine ⟨V, hpV, hV, ?_⟩
  have haff : IsAffine (overRes V).left := hV
  have hne : Nonempty (⊤ : V.toScheme.Opens) := ⟨⟨⟨p, hpV⟩, trivial⟩⟩
  have hnt : Nontrivial Γ((overRes V).left, ⊤) :=
    Scheme.component_nontrivial V.toScheme ⊤
  have mk : ∀ V' : S.Opens, V ≤ T.hom ⁻¹ᵁ V' → (overRes V ⟶ overRes (T := baseOver S) V') :=
    fun V' h => Over.homMk (T.hom.resLE V' V h) (by
      change T.hom.resLE V' V h ≫ V'.ι ≫ 𝟙 S = V.ι ≫ T.hom
      rw [Category.comp_id, Scheme.Hom.resLE_comp_ι])
  have h₀ := mk V₀ fun y hy => (hle hy).1.1
  have h₁ := mk V₁ fun y hy => (hle hy).1.2
  have hWle : ∀ c, V ≤ W c := fun c y hy => Set.mem_iInter.1 (hle hy).2 c
  let hc : ∀ c, overRes V ⟶ overRes (W c) := fun c => Over.homMk (T.left.homOfLE (hWle c)) (by
    change T.left.homOfLE (hWle c) ≫ (W c).ι ≫ T.hom = V.ι ≫ T.hom
    rw [Scheme.homOfLE_ι_assoc])
  have hcι : ∀ c, hc c ≫ overResι (W c) = overResι V := fun c =>
    Over.OverMorphism.ext (T.left.homOfLE_ι (hWle c))
  choose U hU using fun c => exists_theta_pull P.A P.isLB (hc c) (U₀ c)
  have hUpt : ∀ c, (U c).pt = overResι V ≫ x c := fun c => by
    rw [(hU c).1, hU₀, ← Category.assoc, hcι]
  have H := hmul S P m
  rw [← Nat.cast_pow] at H
  obtain ⟨α₀, hα₀⟩ := H
  have hsurj := surjective_mulA P m hm0 α₀ hα₀
  obtain ⟨α, hα, -⟩ := exists_gen_pullTo
    (φ' := ![(snd (overRes V) P.A).left, (snd (overRes V) P.A ^ m).left]) α₀ hα₀
    (snd (overRes V) P.A).left (fun k => by
      fin_cases k
      · exact Category.comp_id _
      · change (snd (overRes V) P.A).left ≫ (mulA P.A m).left = (snd (overRes V) P.A ^ m).left
        rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id])
  let i₀ : Fin (1 ^ P.g) := ⟨0, by simp⟩
  let th : LB.Sec (LPow P.A P.L 1 (overRes V)) := pullS P.A _ h₁ (b₁ i₀)
  obtain ⟨s₁, hs₁⟩ := exists_isTwistPull P.A (ψ := mulT P.A (overRes V) m) (hm := lift_snd _ _) (b := 1)
    P.isLB hα th
  obtain ⟨ρ, hρ, -⟩ := hact S P (m ^ 2 : ℕ) (overRes V)
  let t : (Fin (2 * P.g) → Fin (m ^ 2)) → SecM P.A P.L (m ^ 2 : ℕ) (overRes V) := fun c =>
    ρ (U c) (SecM.ofSec P.A s₁)
  have ht : ∀ c, IsActOf P.A P.L (m ^ 2 : ℕ) (U c) s₁ (SecM.toSec P.A (t c)) := fun c =>
    (hρ _ _ _).2 rfl
  obtain ⟨b, hb⟩ := exists_basis P (m ^ 2) b₀ hb₀ (overRes V) h₀
  have hspan : Submodule.span Γ((overRes V).left, ⊤) (Set.range t) = ⊤ := by
    refine span_eq_top_of_functionals b t fun 𝔪 h𝔪 l hl y => ?_
    obtain ⟨K, _, _, u, hu⟩ := exists_geomPoint (overRes V).left 𝔪 h𝔪
    let w : Spec (CommRingCat.of K) ⟶ S := u ≫ (overRes V).hom
    let h : Over.mk w ⟶ overRes V := Over.homMk u rfl
    have haffK : IsAffine (Over.mk w).left := inferInstanceAs (IsAffine (Spec _))
    have hntK : Nontrivial Γ((Over.mk w).left, ⊤) :=
      (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.domain_nontrivial
    obtain ⟨b', hb'⟩ := exists_basis P (m ^ 2) b₀ hb₀ (Over.mk w) (h ≫ h₀)
    obtain ⟨b₁', hb₁'⟩ := exists_basis P 1 b₁ hb₁ (Over.mk w) (h ≫ h₁)
    refine (hu _).1 (functional_mem_of_span h.left.appTop.hom (pullM P.A P.L (m ^ 2 : ℕ) h) b b'
      (fun i => by rw [hb, hb', pullM_comp P.A P.isLB]) t ?_ l (fun c => (hu _).2 (hl c)) y)
    obtain ⟨ρ', k₁, -, k₃, k₄⟩ := hact S P (m ^ 2 : ℕ) (Over.mk w)
    choose U' hU' using fun c => exists_theta_pull P.A P.isLB h (U c)
    have e : ∀ c, pullM P.A P.L (m ^ 2 : ℕ) h (t c) =
        ρ' (U' c) (SecM.ofSec P.A (pullS P.A _ h s₁)) := fun c =>
      ((k₁ _ _ _).1 ((hU' c).2 _ _ (ht c))).symm
    simp only [e]
    refine span_translates_eq_top P.A (hirr S P K w (m ^ 2) hk
      (by rw [Nat.cast_pow]; exact pow_ne_zero _ (natCast_ne_zero w hunit))) ρ' k₁ k₃ k₄ U'
      (fun θ => ?_) _ fun h0 => ?_
    · obtain ⟨c, hc'⟩ := lev.span K w θ.pt ((hker S P (m ^ 2) (Over.mk w) θ.pt).1 fun _ =>
        ⟨⊤, trivial, _, LB.isGen_genPull _ θ.φ θ.isGen _⟩)
      refine ⟨c, Eq.trans ?_ hc'⟩
      rw [(hU' c).1, hUpt, ← Category.assoc, comp_linComb]
      refine congrArg (fun y => linComb y _) (funext fun i => ?_)
      rw [← Category.assoc]
      refine congrArg (· ≫ lev.pt i) (Over.OverMorphism.ext ?_)
      exact Category.assoc u V.ι T.hom
    · obtain ⟨α', -, k₂⟩ := exists_twist_pull P.A (ψ := mulT P.A (overRes V) m) (hm := lift_snd _ _)
        (b := 1) P.isLB hα h (ψ' := mulT P.A (Over.mk w) m) (lift_snd _ _) (mulT_comm P.A h m)
      have hint : IsIntegral (Over.mk w ⊗ P.A).left :=
        (forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ P.A.hom P.isAb.smooth
          P.isAb.geomConnected).geometrically_isIntegral w _ _
          (IsPullback.of_hasPullback w P.A.hom).flip
      have hz := ofSec_eq_zero_of_twist P.A P.isLB (surjective_mulT P.A m hsurj _) (k₂ _ _ hs₁) h0
      exact b₁'.ne_zero i₀ ((hb₁' i₀).trans ((pullM_comp P.A P.isLB _ h h₁ _).symm.trans hz))
  have hVV : VVsub P (m ^ 2) m (overRes V) = SecM P.A P.L (m ^ 2 : ℕ) (overRes V) := by
    refine le_antisymm (Submodule.span_le.2 fun f hf => hf.1) fun f hf => ?_
    have h1 : Submodule.span Γ((overRes V).left, ⊤) (Set.range t) ≤
        (VVsub P (m ^ 2) m (overRes V)).comap (SecM P.A P.L (m ^ 2 : ℕ) (overRes V)).subtype := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨(t c).2, inVV_of_isVVGen P _ m ⟨th, s₁, α, U c, hα, hs₁, ht c⟩⟩
    exact h1 (x := ⟨f, hf⟩) (hspan.ge trivial)
  rw [hVV]
  exact ⟨Module.Free.of_basis b, by rw [Module.finrank_eq_card_basis b, Fintype.card_fin]⟩
end GlobalTheory.VVRank
