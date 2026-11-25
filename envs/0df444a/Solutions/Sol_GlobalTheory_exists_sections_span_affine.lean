-- Prove2me | solution 1 for GlobalTheory.exists_sections_span_affine
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:28.735159+00:00
-- url     : https://prove2.me/submissions/ef2e9c3c-1680-454a-a247-b5e442f92df8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSectionsSpanAffine
import Theorems.Thm_GlobalTheory_SecAff_pull_pull
import Theorems.Thm_GlobalTheory_SecAff_isPullSec_iff
import Theorems.Thm_GlobalTheory_SecAff_pull_extend
import Theorems.Thm_GlobalTheory_SecAff_pow_smul_mem
import Theorems.Thm_GlobalTheory_SecAff_exists_lift
import Theorems.Thm_P2M_GlobalTheory_SecAff_overRes__range_d148ce4f1708
import Theorems.Thm_GlobalTheory_SecAff_isUnit_pa
import Theorems.Thm_GlobalTheory_SecAff_local_span

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
set_option autoImplicit false
noncomputable section
open GlobalTheory.SecAff
namespace GlobalTheory
theorem _root_.solution :
    SecBaseChangeSt → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (n : ℕ), 1 ≤ n → ∀ U : S.Opens, IsAffineOpen U → ∃ (m : ℕ) (b : Fin (m + 1) → LB.Sec (LPow P.A P.L n (overRes (T := baseOver S) U))), ∀ (T' : Over S) [IsAffine T'.left] (h : T' ⟶ overRes (T := baseOver S) U) (b' : Fin (m + 1) → LB.Sec (LPow P.A P.L n T')), (∀ i, IsPullSec P.A P.L n (h ▷ P.A) (whiskerRight_snd h P.A) (b i) (b' i)) → Submodule.span Γ(T'.left, ⊤) (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T')) = ⊤ := by
  intro H S _ P n hn U hU
  have := P.isAb.proper
  generalize hT : overRes (T := baseOver S) U = T
  have : IsAffine T.left := by subst hT; exact hU
  clear hT hU

  have loc : ∀ p : T.left, ∃ r : Γ(T.left, ⊤), p ∈ T.left.basicOpen r ∧
      ∃ s : Fin (n ^ P.g) → SecM P.A P.L n T, ∀ (T' : Over S) [IsAffine T'.left] (k : T' ⟶ T),
        (∀ x, k.left x ∈ T.left.basicOpen r) →
        Submodule.span Γ(T'.left, ⊤) (Set.range fun i => pull P.A P.L n k (s i)) = ⊤ := by
    intro p
    obtain ⟨V, hp, b, hb⟩ := local_span H S P n hn (T.hom p)
    obtain ⟨r, hr, hpr⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := T.hom ⁻¹ᵁ V)
      ⟨p, hp⟩ trivial
    obtain ⟨g, -⟩ := exists_lift (T := baseOver S) (T' := overRes (T.left.basicOpen r))
      (Over.homMk (overRes (T.left.basicOpen r)).hom (Category.comp_id _)) V
      (fun x => hr x.2)
    choose N s hs using fun i => pull_extend P.A P.L n P.isLB (overResι (T.left.basicOpen r)) r
      (overResι_range _) (pull P.A P.L n g (b i))
    refine ⟨r, hpr, s, fun T' _ k hk => ?_⟩
    obtain ⟨k', rfl⟩ := exists_lift k _ hk
    refine eq_top_iff.2 ((hb T' (k' ≫ g)).ge.trans (Submodule.span_le.2 ?_))
    rintro _ ⟨i, rfl⟩
    have hu := ((isUnit_pa (overResι (T.left.basicOpen r)) r (fun x => x.2)).pow (N i)).map
      (pa k'.left (V := ⊤) (le_pre_top _))
    refine (Submodule.smul_mem_iff_of_isUnit _ hu).1 (Submodule.subset_span ⟨i, ?_⟩)
    simp only
    rw [← pull_pull, hs, map_smulₛₗ, pull_pull]
  choose r hr s hs using loc
  obtain ⟨I, hI⟩ := isCompact_univ.elim_finite_subcover
    (fun p => (T.left.basicOpen (r p) : Set T.left)) (fun p => (T.left.basicOpen (r p)).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hr x⟩)
  let c : Option (I × Fin (n ^ P.g)) → SecM P.A P.L n T := fun o => o.elim 0 fun q => s q.1 q.2
  let e : Option (I × Fin (n ^ P.g)) ≃ Fin (Fintype.card (I × Fin (n ^ P.g)) + 1) :=
    Fintype.equivFinOfCardEq Fintype.card_option
  refine ⟨_, fun i => SecM.toSec P.A (c (e.symm i)), fun T' _ h b' hb' => ?_⟩
  set W := Submodule.span Γ(T'.left, ⊤)
    (Set.range fun i => (SecM.ofSec P.A (b' i) : SecM P.A P.L n T'))
  have hW : ∀ (p : I) i, pull P.A P.L n h (s p i) ∈ W := by
    intro p i
    refine Submodule.subset_span ⟨e (some (p, i)), ?_⟩
    refine ((isPullSec_iff P.A P.L n _ _ _).1 (hb' _)).trans ?_
    simp only [Equiv.symm_apply_apply]
    rfl
  let r' : I → Γ(T'.left, ⊤) := fun p => pa h.left (V := ⊤) (le_pre_top _) (r p)
  have hb : ∀ p x, x ∈ T'.left.basicOpen (r' p) ↔ h.left x ∈ T.left.basicOpen (r p) := by
    intro p x
    change x ∈ T'.left.basicOpen (h.left.appLE ⊤ ⊤ (le_pre_top _) (r p)) ↔ _
    rw [Scheme.basicOpen_appLE]
    exact ⟨fun H => H.2, fun H => ⟨trivial, H⟩⟩
  have hspan : Ideal.span (Set.range r') = ⊤ := by
    rw [← (isAffineOpen_top T'.left).iSup_basicOpen_eq_self_iff]
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := Set.mem_iUnion₂.1 (hI (Set.mem_univ (h.left x)))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r' ⟨p, hp⟩, ⟨_, rfl⟩⟩, (hb _ _).2 hx⟩
  refine eq_top_iff.2 fun σ _ => ?_
  refine Submodule.mem_of_span_eq_top_of_smul_pow_mem W _ hspan σ ?_
  rintro ⟨_, p, rfl⟩
  have : IsAffine (overRes (T'.left.basicOpen (r' p))).left :=
    (isAffineOpen_top T'.left).basicOpen (r' p)
  refine pow_smul_mem P.A P.L n P.isLB (overResι (T'.left.basicOpen (r' p))) (r' p)
    (overResι_range _) W σ ?_
  refine ((hs p _ (overResι (T'.left.basicOpen (r' p)) ≫ h)
    (fun x => (hb p x.1).1 x.2)).ge.trans (Submodule.span_mono ?_)) trivial
  rintro _ ⟨i, rfl⟩
  exact ⟨_, hW p i, pull_pull _ _ _ _ _ _⟩
end GlobalTheory
