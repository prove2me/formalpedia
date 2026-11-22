-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_exists_stages
-- status  : ACCEPTED   (prove)
-- author  : @Miikka
-- created : 2026-11-21T13:45:17.244177+00:00
-- url     : https://prove2.me/submissions/474c1c0c-d5f6-4042-85b7-c50c2b0495cd

import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_exists_cofinal_structuralPairs
import Theorems.Thm_MasulloGRH_schwartzBruhat_averaging

set_option autoImplicit false

namespace Aux_ST

open MasulloGRH

variable {G : Type*} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

noncomputable def ofElemL {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : ElemSchwartz m n r s d →ₗ[ℂ] SchwartzBruhat G where
  toFun := SchwartzBruhat.ofElem Γ k π hs hπ
  map_add' f g := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (f + g).toFun x = extendPullback Γ π f.toFun x + extendPullback Γ π g.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp
  map_smul' c f := by
    apply Subtype.ext
    funext x
    show extendPullback Γ π (c • f).toFun x = c * extendPullback Γ π f.toFun x
    unfold extendPullback
    split_ifs
    · rfl
    · simp

lemma ofElem_inj {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Function.Injective (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  intro g g' h
  apply Subtype.ext
  funext q
  obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd q)
  have h1 : extendPullback Γ π g.toFun (x : G) = extendPullback Γ π g'.toFun (x : G) :=
    congrFun (congrArg Subtype.val h) (x : G)
  unfold extendPullback at h1
  rw [dif_pos x.2, dif_pos x.2] at h1
  simp only [Subtype.coe_eta, hx, toAdd_ofAdd] at h1
  exact h1

end Aux_ST

open MasulloGRH in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    ∃ (m n r s : ℕ → ℕ) (d : (N : ℕ) → Fin (s N) → ℕ)
      (J : (N : ℕ) → ElemSchwartz (m N) (n N) (r N) (s N) (d N) →ₗ[ℂ] SchwartzBruhat G)
      (P : (N : ℕ) → SchwartzBruhat G →ₗ[ℂ] ElemSchwartz (m N) (n N) (r N) (s N) (d N)),
      (∀ N i, d N i ≠ 0) ∧
      (∀ N y, P N (J N y) = y) ∧
      (∀ N M f, N ≤ M → J M (P M (J N (P N f))) = J N (P N f)) ∧
      (∀ N M f, N ≤ M → J N (P N (J M (P M f))) = J N (P N f)) ∧
      (∀ f, ∃ N, J N (P N f) = f) ∧
      (∀ N, ∃ (Γ k : Subgroup G)
        (π : Γ →* Multiplicative (ElemGroup (m N) (n N) (r N) (s N) (d N)))
        (hs : IsStructuralPair Γ k) (hπ : IsElemPresentation Γ k π),
        ∀ y, J N y = SchwartzBruhat.ofElem Γ k π hs hπ y) ∧
      (∀ (Γ k : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
        (π : Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π), ∃ M,
          (∀ g, J M (P M (SchwartzBruhat.ofElem Γ k π hs hπ g)) =
            SchwartzBruhat.ofElem Γ k π hs hπ g) ∧
          Continuous (fun g => P M (SchwartzBruhat.ofElem Γ k π hs hπ g))) ∧
      (∀ N M, Continuous (fun y => P N (J M y))) := by
  obtain ⟨Γ, k, m, n, r, s, d, π, hpair, hmono, hanti, hcof⟩ := exists_cofinal_structuralPairs G
  obtain ⟨A, hA1, hA2, hA3, hA4⟩ := schwartzBruhat_averaging G
  have hs : ∀ N, IsStructuralPair (Γ N) (k N) := fun N => (hpair N).1
  have hπ : ∀ N, IsElemPresentation (Γ N) (k N) (π N) := fun N => (hpair N).2
  let J : (N : ℕ) → ElemSchwartz (m N) (n N) (r N) (s N) (d N) →ₗ[ℂ] SchwartzBruhat G :=
    fun N => Aux_ST.ofElemL (Γ N) (k N) (π N) (hs N) (hπ N)
  have hJ : ∀ N y, J N y = SchwartzBruhat.ofElem (Γ N) (k N) (π N) (hs N) (hπ N) y :=
    fun N y => rfl
  have hinj : ∀ N, Function.Injective (J N) :=
    fun N => Aux_ST.ofElem_inj (Γ N) (k N) (π N) (hs N) (hπ N)
  have hrange : ∀ N f, A (Γ N) (k N) f ∈ LinearMap.range (J N) := fun N f => by
    obtain ⟨g, hg⟩ := hA1 (Γ N) (k N) _ _ _ _ _ (π N) (hs N) (hπ N) f
    exact ⟨g, hg.symm⟩
  let P : (N : ℕ) → SchwartzBruhat G →ₗ[ℂ] ElemSchwartz (m N) (n N) (r N) (s N) (d N) :=
    fun N => (LinearEquiv.ofInjective (J N) (hinj N)).symm.toLinearMap ∘ₗ
      (A (Γ N) (k N)).codRestrict (LinearMap.range (J N)) (hrange N)
  have hJP : ∀ N f, J N (P N f) = A (Γ N) (k N) f := by
    intro N f
    have := LinearEquiv.ofInjective_apply (J N) (h := hinj N)
      ((LinearEquiv.ofInjective (J N) (hinj N)).symm ⟨_, hrange N f⟩)
    rw [LinearEquiv.apply_symm_apply] at this
    exact this.symm
  -- `A N` fixes the stage `N`
  have hfixN : ∀ N y, A (Γ N) (k N) (J N y) = J N y := fun N y =>
    hA2 (Γ N) (k N) _ _ _ _ _ (π N) (hs N) (hπ N) (Γ N) (k N) (hs N) le_rfl le_rfl y
  have hPJ : ∀ N y, P N (J N y) = y := fun N y => hinj N (by rw [hJP, hfixN])
  -- fixed points propagate upwards
  have hup : ∀ N M f, N ≤ M → A (Γ N) (k N) f = f → A (Γ M) (k M) f = f := by
    intro N M f hNM hf
    rw [← hf, ← hJP N f]
    exact hA2 (Γ N) (k N) _ _ _ _ _ (π N) (hs N) (hπ N) (Γ M) (k M) (hs M) (hmono hNM)
      (hanti hNM) _
  have hmono' : ∀ N M f, N ≤ M → J M (P M (J N (P N f))) = J N (P N f) := by
    intro N M f hNM
    rw [hJP M]
    exact hA2 (Γ N) (k N) _ _ _ _ _ (π N) (hs N) (hπ N) (Γ M) (k M) (hs M) (hmono hNM)
      (hanti hNM) _
  have hanti' : ∀ N M f, N ≤ M → J N (P N (J M (P M f))) = J N (P N f) := by
    intro N M f hNM
    rw [hJP N, hJP M, hJP N]
    exact hA3 (Γ N) (k N) (Γ M) (k M) (hs N) (hs M) (hmono hNM) (hanti hNM) f
  -- the transition maps
  have htr : ∀ (Γ' k' : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π' : ↥Γ' →* Multiplicative (ElemGroup m' n' r' s' d')) (hs' : IsStructuralPair Γ' k')
      (hπ' : IsElemPresentation Γ' k' π') (N : ℕ),
      Continuous (fun g => P N (SchwartzBruhat.ofElem Γ' k' π' hs' hπ' g)) := by
    intro Γ' k' m' n' r' s' d' π' hs' hπ' N
    obtain ⟨T, hTc, hT⟩ := hA4 Γ' k' m' n' r' s' d' π' hs' hπ' (Γ N) (k N) _ _ _ _ _ (π N)
      (hs N) (hπ N)
    have e : (fun g => P N (SchwartzBruhat.ofElem Γ' k' π' hs' hπ' g)) = T := by
      funext g
      apply hinj N
      rw [hJP, hT]
      rfl
    rw [e]; exact hTc
  refine ⟨m, n, r, s, d, J, P, fun N => (hπ N).1, hPJ, hmono', hanti', ?_,
    fun N => ⟨Γ N, k N, π N, hs N, hπ N, fun y => rfl⟩, ?_, ?_⟩
  · intro f
    suffices H : ∀ (x : G → ℂ) (hx : x ∈ schwartzBruhatSubmodule G),
        ∃ N, A (Γ N) (k N) ⟨x, hx⟩ = ⟨x, hx⟩ by
      obtain ⟨N, hN⟩ := H f.1 f.2
      exact ⟨N, by rw [hJP]; exact hN⟩
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨Γ', k', m', n', r', s', d', π', g, hs', hπ', rfl⟩ := hx
      obtain ⟨M, h1, h2⟩ := hcof Γ' k' m' n' r' s' d' π' hs' hπ'
      exact ⟨M, hA2 Γ' k' _ _ _ _ _ π' hs' hπ' (Γ M) (k M) (hs M) h1 h2 g⟩
    | zero => exact ⟨0, map_zero _⟩
    | add x y hx hy ihx ihy =>
      obtain ⟨N₁, h₁⟩ := ihx
      obtain ⟨N₂, h₂⟩ := ihy
      refine ⟨max N₁ N₂, ?_⟩
      have e : (⟨x + y, Submodule.add_mem _ hx hy⟩ : SchwartzBruhat G) =
          (⟨x, hx⟩ : SchwartzBruhat G) + ⟨y, hy⟩ := rfl
      rw [e]
      refine (map_add (A _ _) _ _).trans ?_
      rw [hup N₁ _ _ (le_max_left _ _) h₁, hup N₂ _ _ (le_max_right _ _) h₂]
      rfl
    | smul a x hx ihx =>
      obtain ⟨N, h⟩ := ihx
      refine ⟨N, ?_⟩
      have e : (⟨a • x, Submodule.smul_mem _ a hx⟩ : SchwartzBruhat G) =
          a • (⟨x, hx⟩ : SchwartzBruhat G) := rfl
      rw [e]
      refine (map_smul (A _ _) _ _).trans ?_
      rw [h]
      rfl
  · intro Γ' k' m' n' r' s' d' π' hs' hπ'
    obtain ⟨M, h1, h2⟩ := hcof Γ' k' m' n' r' s' d' π' hs' hπ'
    refine ⟨M, fun g => ?_, htr Γ' k' m' n' r' s' d' π' hs' hπ' M⟩
    rw [hJP]
    exact hA2 Γ' k' _ _ _ _ _ π' hs' hπ' (Γ M) (k M) (hs M) h1 h2 g
  · intro N M
    exact htr (Γ M) (k M) _ _ _ _ _ (π M) (hs M) (hπ M) N
