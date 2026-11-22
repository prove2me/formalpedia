-- Prove2me | solution 1 for MasulloGRH.schwartzBruhat_stage_isEmbedding_and_bounded
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T15:44:14.451312+00:00
-- url     : https://prove2.me/submissions/62e58891-28e1-4ba1-9771-879baf8bccd1

import Mathlib
import Definitions.Def_MasulloGRH_SchwartzBruhat
import Theorems.Thm_MasulloGRH_schwartzBruhat_averaging
import Theorems.Thm_MasulloGRH_elemSchwartz_frechet_nuclear_montel
import Theorems.Thm_MasulloGRH_schwartzBruhat_main_structure
import Theorems.Thm_MasulloGRH_bounded_sets_strict_inductive_limit
import Theorems.Thm_MasulloGRH_schwartzBruhat_exists_stages

open Topology

set_option autoImplicit false

namespace Sol_MasulloGRH_schwartzBruhat_stage_isEmbedding_and_bounded

open MasulloGRH

universe u

variable {G : Type u} [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G]

lemma topology_eq : instTopologicalSpaceSchwartzBruhat G =
    sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
    ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      @Continuous (ElemSchwartz m n r s d) (SchwartzBruhat G) _ t
        (SchwartzBruhat.ofElem Γ k π hs hπ)} := rfl

lemma ofElem_continuous {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Continuous (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  rw [continuous_iff_le_induced, topology_eq, ← continuous_iff_le_induced, continuous_sInf_rng]
  intro t ht
  exact ht.2 Γ k m n r s d π hs hπ

lemma elem_ext {m n r s : ℕ} {d : Fin s → ℕ} {g g' : ElemSchwartz m n r s d}
    (h : g.toFun = g'.toFun) : g = g' := Subtype.ext h

lemma ofElem_injective {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : Function.Injective (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  intro g g' h
  have h' : extendPullback Γ π g.toFun = extendPullback Γ π g'.toFun := congrArg Subtype.val h
  apply elem_ext
  funext y
  obtain ⟨x, hx⟩ := hπ.2.2.2.1 (Multiplicative.ofAdd y)
  have := congrFun h' (x : G)
  simp only [extendPullback, dif_pos x.2, Subtype.coe_eta, hx, toAdd_ofAdd] at this
  exact this

lemma ofElem_add {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (g g' : ElemSchwartz m n r s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ (g + g') =
      SchwartzBruhat.ofElem Γ k π hs hπ g + SchwartzBruhat.ofElem Γ k π hs hπ g' := by
  apply Subtype.ext
  show extendPullback Γ π (g + g').toFun = extendPullback Γ π g.toFun + extendPullback Γ π g'.toFun
  funext x
  simp only [extendPullback, Pi.add_apply]
  split_ifs
  · rfl
  · simp

lemma ofElem_smul {m n r s : ℕ} {d : Fin s → ℕ} (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) (c : ℂ) (g : ElemSchwartz m n r s d) :
    SchwartzBruhat.ofElem Γ k π hs hπ (c • g) = c • SchwartzBruhat.ofElem Γ k π hs hπ g := by
  apply Subtype.ext
  show extendPullback Γ π (c • g).toFun = c • extendPullback Γ π g.toFun
  funext x
  simp only [extendPullback, Pi.smul_apply]
  split_ifs
  · rfl
  · simp

/-- Universal property of the inductive limit topology of `S(G)` for linear maps into a locally
convex space. -/
lemma continuous_of_forall_ofElem {F : Type} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (hF : IsLocallyConvexTopology F ‹_›) (L : SchwartzBruhat G →ₗ[ℂ] F)
    (hL : ∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
      (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π),
      Continuous (fun g => L (SchwartzBruhat.ofElem Γ k π hs hπ g))) :
    Continuous L := by
  obtain ⟨ι, hι, p, hp⟩ := hF
  rw [continuous_iff_le_induced, topology_eq]
  refine sInf_le ⟨?_, ?_⟩
  · refine ⟨ULift.{u} ι, inferInstance, fun i => (p i.down).comp L, ?_⟩
    have h1 := LinearMap.withSeminorms_induced hp L
    let _ : TopologicalSpace (SchwartzBruhat G) := TopologicalSpace.induced L inferInstance
    refine h1.congr ?_ ?_
    · intro i
      refine ⟨{i.down}, 1, ?_⟩
      simp [SeminormFamily.comp]
    · intro i
      refine ⟨{ULift.up i}, 1, ?_⟩
      simp [SeminormFamily.comp]
  · intro Γ k m n r s d π hs hπ
    exact continuous_induced_rng.2 (hL Γ k m n r s d π hs hπ)

lemma exists_leftInverse [T2Space G] [LocallyCompactSpace G] {m n r s : ℕ} {d : Fin s → ℕ}
    (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) :
    ∃ L : SchwartzBruhat G →ₗ[ℂ] ElemSchwartz m n r s d, Continuous L ∧
      ∀ g, L (SchwartzBruhat.ofElem Γ k π hs hπ g) = g := by
  obtain ⟨A, h1, h2, -, h4⟩ := schwartzBruhat_averaging G
  have hinj := ofElem_injective Γ k π hs hπ
  choose ℓ hℓ using h1 Γ k m n r s d π hs hπ
  let L : SchwartzBruhat G →ₗ[ℂ] ElemSchwartz m n r s d :=
    { toFun := ℓ
      map_add' := fun f f' => hinj (by rw [← hℓ, ofElem_add, ← hℓ, ← hℓ, map_add])
      map_smul' := fun c f => hinj (by rw [← hℓ, RingHom.id_apply, ofElem_smul, ← hℓ, map_smul]) }
  refine ⟨L, ?_, fun g => hinj (by
    show SchwartzBruhat.ofElem Γ k π hs hπ (ℓ _) = _
    rw [← hℓ]; exact h2 Γ k m n r s d π hs hπ Γ k hs le_rfl le_rfl g)⟩
  refine continuous_of_forall_ofElem (elemSchwartz_frechet_nuclear_montel m n r s d hπ.1).1.1 L ?_
  intro Γ' k' m' n' r' s' d' π' hs' hπ'
  obtain ⟨T, hT, hTeq⟩ := h4 Γ' k' m' n' r' s' d' π' hs' hπ' Γ k m n r s d π hs hπ
  have : (fun g => L (SchwartzBruhat.ofElem Γ' k' π' hs' hπ' g)) = T := by
    funext g
    exact hinj ((hℓ _).symm.trans (hTeq g))
  rw [this]
  exact hT

lemma ofElem_isEmbedding [T2Space G] [LocallyCompactSpace G] {m n r s : ℕ} {d : Fin s → ℕ}
    (Γ k : Subgroup G)
    (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
    (hπ : IsElemPresentation Γ k π) : IsEmbedding (SchwartzBruhat.ofElem Γ k π hs hπ) := by
  obtain ⟨L, hLc, hL⟩ := exists_leftInverse Γ k π hs hπ
  exact Function.LeftInverse.isEmbedding (f := L) hL hLc (ofElem_continuous Γ k π hs hπ)

lemma bounded_part [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G]
    (B : Set (SchwartzBruhat G)) (hB : Bornology.IsVonNBounded ℂ B) :
    ∃ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (B' : Set (ElemSchwartz m n r s d)),
        Bornology.IsVonNBounded ℂ B' ∧ B = SchwartzBruhat.ofElem Γ k π hs hπ '' B' := by
  obtain ⟨m, n, r, s, d, J, P, -, hPJ, hmono1, -, hexh, hstage, hfac, -⟩ :=
    schwartzBruhat_exists_stages G
  have hHLCS : IsHLCS (SchwartzBruhat G) := (schwartzBruhat_main_structure G).1
  have : T2Space (SchwartzBruhat G) := hHLCS.2
  choose Γs ks πs hss hπs hJ using hstage
  choose LN hLNc hLN using fun N => exists_leftInverse (Γs N) (ks N) (πs N) (hss N) (hπs N)
  have hJc : ∀ N, Continuous (J N) := fun N => by
    have : (J N : _ → _) = SchwartzBruhat.ofElem (Γs N) (ks N) (πs N) (hss N) (hπs N) :=
      funext (hJ N)
    rw [this]
    exact ofElem_continuous _ _ _ _ _
  let X : ℕ → Submodule ℂ (SchwartzBruhat G) := fun N => LinearMap.range (J N)
  have hmono : Monotone X := by
    intro N M hNM f hf
    obtain ⟨y, rfl⟩ := hf
    exact ⟨P M (J N (P N (J N y))), by rw [hmono1 N M (J N y) hNM, hPJ]⟩
  have hexh' : ∀ f : SchwartzBruhat G, ∃ N, f ∈ X N := fun f => by
    obtain ⟨N, hN⟩ := hexh f
    exact ⟨N, P N f, hN⟩
  have hfix : ∀ N, ∀ f ∈ X N, J N (LN N f) = f := by
    intro N f hf
    obtain ⟨y, rfl⟩ := hf
    rw [hJ N y, hLN N y]
    exact hJ N y
  have hcl : ∀ N, IsClosed (X N : Set (SchwartzBruhat G)) := by
    intro N
    have : (X N : Set (SchwartzBruhat G)) = {f | J N (LN N f) = f} := by
      ext f
      exact ⟨fun hf => hfix N f hf, fun hf => ⟨LN N f, hf⟩⟩
    rw [this]
    exact isClosed_eq ((hJc N).comp (hLNc N)) continuous_id
  have hfacX : ∀ (Γ k : Subgroup G) (m' n' r' s' : ℕ) (d' : Fin s' → ℕ)
      (π : ↥Γ →* Multiplicative (ElemGroup m' n' r' s' d')) (hs : IsStructuralPair Γ k)
      (hπ : IsElemPresentation Γ k π), ∃ (M : ℕ) (φ : ElemSchwartz m' n' r' s' d' → X M),
        Continuous φ ∧ SchwartzBruhat.ofElem Γ k π hs hπ = Subtype.val ∘ φ := by
    intro Γ k m' n' r' s' d' π hs hπ
    obtain ⟨M, hM1, hM2⟩ := hfac Γ k m' n' r' s' d' π hs hπ
    refine ⟨M, fun g => ⟨J M (P M (SchwartzBruhat.ofElem Γ k π hs hπ g)), ⟨_, rfl⟩⟩,
      Continuous.subtype_mk ((hJc M).comp hM2) _, ?_⟩
    funext g
    exact (hM1 g).symm
  have htop : instTopologicalSpaceSchwartzBruhat G =
      sInf {t | IsLocallyConvexTopology (SchwartzBruhat G) t ∧
        ∀ N, @Continuous (X N) (SchwartzBruhat G) _ t Subtype.val} := by
    apply le_antisymm
    · refine le_sInf ?_
      rintro t ⟨htlc, htc⟩
      rw [topology_eq]
      refine sInf_le ⟨htlc, ?_⟩
      intro Γ k m' n' r' s' d' π hs hπ
      obtain ⟨M, φ, hφ, heq⟩ := hfacX Γ k m' n' r' s' d' π hs hπ
      rw [heq]
      exact @Continuous.comp (ElemSchwartz m' n' r' s' d') (X M) (SchwartzBruhat G) _
        (@instTopologicalSpaceSubtype _ _ (instTopologicalSpaceSchwartzBruhat G)) t _ _ (htc M) hφ
    · exact sInf_le ⟨hHLCS.1, fun N => continuous_subtype_val⟩
  obtain ⟨N, B', -, hBeq⟩ :=
    (bounded_sets_strict_inductive_limit (SchwartzBruhat G) hHLCS X hmono hexh' hcl htop B).1 hB
  have hBX : ∀ f ∈ B, f ∈ X N := by
    intro f hf
    rw [hBeq] at hf
    obtain ⟨b, -, rfl⟩ := hf
    exact b.2
  let LNc : SchwartzBruhat G →L[ℂ] ElemSchwartz (m N) (n N) (r N) (s N) (d N) :=
    ⟨LN N, hLNc N⟩
  refine ⟨Γs N, ks N, m N, n N, r N, s N, d N, πs N, hss N, hπs N, LN N '' B,
    hB.image LNc, ?_⟩
  ext f
  constructor
  · intro hf
    refine ⟨LN N f, ⟨f, hf, rfl⟩, ?_⟩
    rw [← hJ N]
    exact hfix N f (hBX f hf)
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    rw [← hJ N, hfix N f (hBX f hf)]
    exact hf

end Sol_MasulloGRH_schwartzBruhat_stage_isEmbedding_and_bounded

open MasulloGRH Sol_MasulloGRH_schwartzBruhat_stage_isEmbedding_and_bounded in
theorem solution
    (G : Type*) [CommGroup G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] :
    (∀ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π),
        IsEmbedding (SchwartzBruhat.ofElem Γ k π hs hπ)) ∧
    (∀ B : Set (SchwartzBruhat G), Bornology.IsVonNBounded ℂ B →
      ∃ (Γ k : Subgroup G) (m n r s : ℕ) (d : Fin s → ℕ)
        (π : ↥Γ →* Multiplicative (ElemGroup m n r s d)) (hs : IsStructuralPair Γ k)
        (hπ : IsElemPresentation Γ k π) (B' : Set (ElemSchwartz m n r s d)),
        Bornology.IsVonNBounded ℂ B' ∧ B = SchwartzBruhat.ofElem Γ k π hs hπ '' B') :=
  ⟨fun Γ k _ _ _ _ _ π hs hπ => ofElem_isEmbedding Γ k π hs hπ,
    fun B hB => bounded_part B hB⟩
