-- Prove2me | solution 1 for NumberField.SUnits.isGlobalBridge2_apply_inflation_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/b17c4908-67ad-5f7a-bb63-5366c67c5c2c

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import Theorems.Thm_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace INFE2TK

lemma isUnramifiedOutside_iSup (S : Finset Nat.Primes) {ι : Type} [Finite ι] (F : ι → IntermediateField ℚ (AlgebraicClosure ℚ))
    (hF : ∀ i, (F i).IsUnramifiedOutside S) : (⨆ i, F i).IsUnramifiedOutside S := by
  haveI := Fintype.ofFinite ι
  rw [← Finset.sup_univ_eq_iSup]
  exact Finset.sup_induction (p := fun E : IntermediateField ℚ (AlgebraicClosure ℚ) => E.IsUnramifiedOutside S)
    (IntermediateField.isUnramifiedOutside_bot S)
    (fun a (ha : a.IsUnramifiedOutside S) b (hb : b.IsUnramifiedOutside S) => ha.sup hb) (fun i _ => hF i)

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

def ev (ψ : (ihom (Rep.res π P)).obj A) : P →+ A := LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

lemma ev_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ + ψ') x = ev π ψ x + ev π ψ' x := rfl
lemma ev_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ - ψ') x = ev π ψ x - ev π ψ' x := rfl

lemma ρ_ρ_inv {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d (V.ρ d⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hκ in

lemma κ_inj {m m' : M} (h : ∀ b, κ b m = κ b m') : m = m' :=
  (hκ (κ.flip m')).unique h (fun _ => rfl)

include hfg hg hκ in

lemma exists_forall_κ_eq (c : P →+ A) (hc : ∀ x : R, c (f.hom x) = 0) : ∃ m : M, ∀ x : P, κ (g.hom x) m = c x := by
  classical

  have hker : ∀ y y' : P, g.hom y = g.hom y' → c y = c y' := by
    intro y y' hyy'
    have h0 : g.hom (y - y') = 0 := by rw [map_sub, hyy', sub_self]
    obtain ⟨x, hx⟩ := (hfg _).1 h0
    have := hc x
    rw [hx, map_sub, sub_eq_zero] at this
    exact this
  let s : B → P := Function.surjInv hg
  have hs : ∀ b, g.hom (s b) = b := Function.surjInv_eq hg
  let cB : B →+ A :=
    { toFun := fun b => c (s b)
      map_zero' := by rw [hker (s 0) 0 (by rw [hs, map_zero]), map_zero]
      map_add' := fun b b' => by rw [← map_add, hker (s (b + b')) (s b + s b') (by rw [hs, map_add, hs, hs])] }
  obtain ⟨m, hm, -⟩ := hκ cB
  exact ⟨m, fun x => by rw [hm]; exact hker _ _ (hs _)⟩

include hκeq in

lemma κ_ρ (h : H) (b : B) (m : M) : κ b (M.ρ h m) = A.ρ h (κ (B.ρ (π h⁻¹) b) m) := by
  rw [← hκeq, map_inv, ρ_ρ_inv]

lemma ev_ρ (h : H) (t : (ihom (Rep.res π P)).obj A) (x : P) :
    ev π (((ihom (Rep.res π P)).obj A).ρ h t) x = A.ρ h (ev π t (P.ρ (π h⁻¹) x)) := rfl

def evD {V W : Rep.{0} k D} (t : (ihom V).obj W) : V →+ W := LinearMap.toAddMonoidHom (show V →ₗ[k] W from t)

lemma evD_add {V W : Rep.{0} k D} (s t : (ihom V).obj W) (x : V) : evD (s + t) x = evD s x + evD t x := rfl
lemma evD_sub {V W : Rep.{0} k D} (s t : (ihom V).obj W) (x : V) : evD (s - t) x = evD s x - evD t x := rfl
lemma evD_zero {V W : Rep.{0} k D} (x : V) : evD (0 : (ihom V).obj W) x = 0 := rfl
lemma evD_ρ {V W : Rep.{0} k D} (d : D) (t : (ihom V).obj W) (x : V) :
    evD (((ihom V).obj W).ρ d t) x = W.ρ d (evD t (V.ρ d⁻¹ x)) := rfl

lemma cocycle_evD (a : D → (ihom R).obj X) (ha : a ∈ cocycles₁ ((ihom R).obj X)) (d₁ d₂ : D) (x : R) :
    X.ρ d₁ (evD (a d₂) (R.ρ d₁⁻¹ x)) - evD (a (d₁ * d₂)) x + evD (a d₁) x = 0 := by
  have h := (mem_cocycles₁_iff a).1 ha d₁ d₂
  have := congrArg (fun t => evD t x) h
  simp only [evD_add, evD_ρ] at this
  rw [this]
  abel

noncomputable def cob₂ (Φ : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) : P →+ A := ev π ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom Φ (g₁, g₂))

lemma cob₂_apply (Φ : H → (ihom (Rep.res π P)).obj A) (g₁ g₂ : H) (x : P) :
    cob₂ π Φ g₁ g₂ x = A.ρ g₁ (ev π (Φ g₂) (P.ρ (π g₁⁻¹) x)) - ev π (Φ (g₁ * g₂)) x + ev π (Φ g₁) x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ g₁ (Φ g₂) - Φ (g₁ * g₂) + Φ g₁) x = _
  rfl

include hιeq in

lemma cob₂_apply_f (a : D → (ihom R).obj X) (ha : a ∈ cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ (d : D) (x : R), ev π (ψ d) (f.hom x) = ι (evD (a d) x)) (g₁ g₂ : H) (x : R) :
    cob₂ π (ψ ∘ π) g₁ g₂ (f.hom x) = 0 := by
  simp only [cob₂_apply, Function.comp_apply]
  rw [← Rep.hom_comm_apply f, hψ, hψ, hψ, ← hιeq, ← map_sub ι, ← map_add ι, map_mul, map_inv, cocycle_evD a ha, map_zero]

noncomputable def mOf₂ (Φ : H → (ihom (Rep.res π P)).obj A) (gg : H × H) : M := by
  classical
  exact if hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π Φ gg.1 gg.2 x then hex.choose else 0

include hfg hg hκ hιeq in
lemma κ_mOf₂ (a : D → (ihom R).obj X) (ha : a ∈ cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ (d : D) (x : R), ev π (ψ d) (f.hom x) = ι (evD (a d) x)) (g₁ g₂ : H) (x : P) :
    κ (g.hom x) (mOf₂ π g κ (ψ ∘ π) (g₁, g₂)) = cob₂ π (ψ ∘ π) g₁ g₂ x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π (ψ ∘ π) g₁ g₂ x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob₂ π (ψ ∘ π) g₁ g₂) (cob₂_apply_f π f ι hιeq a ha ψ hψ g₁ g₂)
  simp only [mOf₂, dif_pos hex]
  exact hex.choose_spec x

include hg hκ hκeq in

lemma mem_cocycles₂_of_forall_κ (Φ : H → (ihom (Rep.res π P)).obj A) (m : H × H → M)
    (hm : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) = cob₂ π Φ g₁ g₂ x) : m ∈ cocycles₂ M := by
  rw [mem_cocycles₂_iff]
  intro g₁ g₂ g₃
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  have hΦ := (mem_cocycles₂_iff _).1 (d₁₂_apply_mem_cocycles₂ (A := (ihom (Rep.res π P)).obj A) Φ) g₁ g₂ g₃
  have hΦx := congrArg (fun t => ev π t x) hΦ
  simp only [ev_add, ev_ρ] at hΦx
  rw [map_add, map_add, hm, hm, hm, κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hm]
  exact hΦx

include hg hκ in

lemma isLevelConstantS₂_of_forall_κ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Finset Nat.Primes)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ (d : D) (x : P), A.ρ s (ev π (ψ d) x) = ev π (ψ d) x)
    (m : H × H → M) (hm : ∀ (g₁ g₂ : H) (x : P), κ (g.hom x) (m (g₁, g₂)) = cob₂ π (ψ ∘ π) g₁ g₂ x) :
    ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ (g₁ g₂ s s' : H), r s ∈ F.fixingSubgroup → r s' ∈ F.fixingSubgroup → m (g₁ * s, g₂ * s') = m (g₁, g₂) := by
  obtain ⟨F₁, hF₁, h₁⟩ := hπlev
  obtain ⟨F₂, hF₂, h₂⟩ := hψlev
  refine ⟨F₁ ⊔ F₂, hF₁.sup hF₂, fun g₁ g₂ s s' hs hs' => ?_⟩
  have hs₁ : π s = 1 := h₁ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
  have hs'₁ : π s' = 1 := h₁ s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs')
  have hs₂ := h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hm, hm, cob₂_apply, cob₂_apply]
  simp only [Function.comp_apply, map_mul π, map_inv π, hs₁, hs'₁, mul_one, mul_inv_rev, inv_one, one_mul, map_mul (A.ρ),
    Module.End.mul_apply, hs₂]

end hyps

section infl

variable {H D D' : Type} [Group H] [Group D] [Group D'] (πF : H →* D) (πF' : H →* D') (π : D' →* D)
  {P : Rep.{0} k D} {P' : Rep.{0} k D'} (ρP : P' ⟶ Rep.res π P) {A : Rep.{0} k H}

def infl (t : (ihom (Rep.res πF P)).obj A) : (ihom (Rep.res πF' P')).obj A :=
  show P' →ₗ[k] A from (show P →ₗ[k] A from t) ∘ₗ ρP.hom.toLinearMap

lemma ev_infl (t : (ihom (Rep.res πF P)).obj A) (y : P') : ev πF' (infl πF πF' π ρP t) y = ev πF t (ρP.hom y) := rfl

lemma cob₂_infl (hπ : ∀ h : H, π (πF' h) = πF h) (ψ : D → (ihom (Rep.res πF P)).obj A) (g₁ g₂ : H) (x' : P') :
    cob₂ πF' ((fun d' => infl πF πF' π ρP (ψ (π d'))) ∘ πF') g₁ g₂ x' = cob₂ πF (ψ ∘ πF) g₁ g₂ (ρP.hom x') := by
  rw [cob₂_apply, cob₂_apply]
  simp only [Function.comp_apply, ev_infl, hπ, map_inv, Rep.hom_comm_apply ρP, Rep.res_obj_ρ, MonoidHom.comp_apply, map_mul]

end infl

theorem core (S : Finset Nat.Primes)
    {D D' : Type} [Group D] [Finite D] [Group D']
    (πF : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* D) (πF' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* D')
    (π : D' →* D) (hπ : ∀ σ, π (πF' σ) = πF σ)
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
      ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → πF s = 1)
    {R P B : Rep ℤ D} (f : R ⟶ P) (g : P ⟶ B) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {R' P' : Rep ℤ D'} (f' : R' ⟶ P') (g' : P' ⟶ Rep.res π B)
    (ρR : R' ⟶ Rep.res π R) (ρP : P' ⟶ Rep.res π P)
    (hρf : f' ≫ ρP = ρR ≫ (Rep.resFunctor π).map f) (hρg : g' = ρP ≫ (Rep.resFunctor π).map g)
    {X : Rep ℤ D} {X' : Rep ℤ D'} {A : Rep ℤ (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
    (ι : X →+ A) (ι' : X' →+ A) (hιeq : ∀ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : X), ι (X.ρ (πF h) x) = A.ρ h (ι x))
    (jE : Rep.res π X ⟶ X') (hjE : ∀ x, ι' (jE.hom x) = ι x)
    {p : ℕ} {M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)} (κ : B →+ M →+ A)
    (hκeq : ∀ (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M), κ (B.ρ (πF h) b) (M.ρ h m) = A.ρ h (κ b m))
    (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)
    (hdiv : ∀ φ : R →+ X, ∃ ψ : (ihom (Rep.res πF P)).obj A,
      (∀ x : R, LinearMap.toAddMonoidHom ψ (f.hom x) = ι (φ x)) ∧
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧
        ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → ∀ x : P,
          A.ρ s (LinearMap.toAddMonoidHom ψ x) = LinearMap.toAddMonoidHom ψ x)
    {ΛE : H1 ((ihom R).obj X) →+ continuousH2S S M} (hΛE : IsGlobalBridge₂ S πF f g ι κ ΛE)
    {ΛE' : H1 ((ihom R').obj X') →+ continuousH2S S M} (hΛE' : IsGlobalBridge₂ S πF' f' g' ι' κ ΛE')
    (a : cocycles₁ ((ihom R).obj X)) (a' : cocycles₁ ((ihom R').obj X'))
    (ha' : ∀ (d' : D') (x' : R'), evD ((a' : D' → _) d') x' = jE.hom (evD ((a : D → _) (π d')) (ρR.hom x'))) :
    ΛE' ((H1π _).hom a') = ΛE ((H1π _).hom a) := by
  classical

  choose Ψ hΨ FΨ hFΨ using hdiv
  let ψ : D → (ihom (Rep.res πF P)).obj A := fun d => Ψ (evD ((a : D → _) d))
  have hψ : ∀ (d : D) (x : R), ev πF (ψ d) (f.hom x) = ι (evD ((a : D → _) d) x) := fun d x => hΨ _ x
  have hψlev : ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₂.IsUnramifiedOutside S ∧
      ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₂.fixingSubgroup → ∀ (d : D) (x : P),
        A.ρ s (ev πF (ψ d) x) = ev πF (ψ d) x := by
    refine ⟨⨆ d, FΨ (evD ((a : D → _) d)), isUnramifiedOutside_iSup S _ (fun d => (hFΨ _).1),
      fun s hs d x => (hFΨ (evD ((a : D → _) d))).2 s ?_ x⟩
    exact IntermediateField.fixingSubgroup_antitone (le_iSup (fun d => FΨ (evD ((a : D → _) d))) d) hs

  have hm := κ_mOf₂ πF f g ι κ hfg hg hιeq hκ a a.2 ψ hψ
  have hcoc := mem_cocycles₂_of_forall_κ πF g κ hg hκeq hκ _ _ hm
  have hlc := isLevelConstantS₂_of_forall_κ πF g κ hg hκ (MonoidHom.id _) S hπlev ψ hψlev _ hm
  have hmem := (mem_levelCocyclesS₂_iff S M _).2 ⟨hcoc, hlc⟩
  have h₁ := hΛE a ψ hψ hψlev _ hm hmem

  let ψ' : D' → (ihom (Rep.res πF' P')).obj A := fun d' => infl πF πF' π ρP (ψ (π d'))
  have hρfx : ∀ x' : R', ρP.hom (f'.hom x') = f.hom (ρR.hom x') := fun x' => by
    have := congrArg (fun χ => Rep.Hom.hom χ x') hρf
    simpa using this
  have hρgx : ∀ x' : P', g'.hom x' = g.hom (ρP.hom x') := fun x' => by
    have := congrArg (fun χ => Rep.Hom.hom χ x') hρg
    simpa using this
  have hψ' : ∀ (d' : D') (x' : R'), ev πF' (ψ' d') (f'.hom x') = ι' (evD ((a' : D' → _) d') x') := by
    intro d' x'
    rw [ha', hjE]
    change ev πF (ψ (π d')) (ρP.hom (f'.hom x')) = _
    rw [hρfx]
    exact hψ (π d') (ρR.hom x')
  have hψ'lev : ∃ F₂ : IntermediateField ℚ (AlgebraicClosure ℚ), F₂.IsUnramifiedOutside S ∧
      ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₂.fixingSubgroup → ∀ (d' : D') (x' : P'),
        A.ρ s (ev πF' (ψ' d') x') = ev πF' (ψ' d') x' := by
    obtain ⟨F₂, hF₂, h₂⟩ := hψlev
    exact ⟨F₂, hF₂, fun s hs d' x' => h₂ s hs (π d') (ρP.hom x')⟩
  have hm' : ∀ (g₁ g₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x' : P'),
      κ (g'.hom x') (mOf₂ πF g κ (ψ ∘ πF) (g₁, g₂)) = cob₂ πF' (ψ' ∘ πF') g₁ g₂ x' := by
    intro g₁ g₂ x'
    rw [hρgx, hm]
    exact (cob₂_infl πF πF' π ρP hπ ψ g₁ g₂ x').symm
  have h₂ := hΛE' a' ψ' hψ' hψ'lev _ hm' hmem
  exact h₂.trans h₁.symm

end INFE2TK

open INFE2TK in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F F' : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] [NumberField ↥F'] [IsGalois ℚ ↥F']
    (hFF' : F ≤ F') (hF : F.IsUnramifiedOutside S) (hF' : F'.IsUnramifiedOutside S)
    (π : (↥F' ≃ₐ[ℚ] ↥F') →* (↥F ≃ₐ[ℚ] ↥F))
    (hπ : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, π (AlgEquiv.restrictNormalHom ↥F' σ) = AlgEquiv.restrictNormalHom ↥F σ)

    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    {R' P' : Rep ℤ (↥F' ≃ₐ[ℚ] ↥F')} (f' : R' ⟶ P') (g' : P' ⟶ Rep.res π B)
    (hf' : Function.Injective f'.hom) (hfg' : Function.Exact f'.hom g'.hom) (hg' : Function.Surjective g'.hom)
    [Module.Finite ℤ P] [Module.Finite ℤ P'] (hB : ∀ b : B, p • b = 0)
    (ρR : R' ⟶ Rep.res π R) (ρP : P' ⟶ Rep.res π P)
    (hρf : f' ≫ ρP = ρR ≫ (Rep.resFunctor π).map f) (hρg : g' = ρP ≫ (Rep.resFunctor π).map g)

    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (ιE' : NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE' : ∀ x, Additive.toMul (ιE' x) = Units.map (algebraMap ↥F' (AlgebraicClosure ℚ) : ↥F' →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F' Sℚ x))
    (jE : Rep.res π (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)
    (hjE : ∀ x, ιE' (jE.hom x) = ιE x)

    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)

    {ΛE : H1 ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {ΛE' : H1 ((ihom R').obj (NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)) →+ continuousH2S S M}
    (hΛE' : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F') f' g' (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE'
      (show Rep.res π B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ from κ) ΛE')

    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (a' : cocycles₁ ((ihom R').obj (NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ)))
    (ha' : ∀ (d' : (↥F' ≃ₐ[ℚ] ↥F')) (x' : R'),
      LinearMap.toAddMonoidHom ((a' : _ → _) d') x' = jE.hom (LinearMap.toAddMonoidHom ((a : _ → _) (π d')) (ρR.hom x'))) :
    ΛE' ((H1π _).hom a') = ΛE ((H1π _).hom a) := by

  have hιeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ),
      ιE ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x) =
        (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (ιE x) := by
    intro γ x
    apply Additive.toMul.injective
    ext
    rw [hιE, Units.coe_map, MonoidHom.coe_coe, NumberField.SUnits.val_rho]
    change algebraMap (↥F) (AlgebraicClosure ℚ) (γ.restrictNormal (↥F) (NumberField.SUnits.val ℚ (↥F) Sℚ x : ↥F)) =
      ((γ • Additive.toMul (ιE x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [hιE]
    change _ = γ ((Units.map (algebraMap (↥F) (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ)
      (NumberField.SUnits.val ℚ (↥F) Sℚ x) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
    rw [AlgEquiv.restrictNormal_commutes, Units.coe_map, MonoidHom.coe_coe]

  have hπlev : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), F₀.IsUnramifiedOutside S ∧
      ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₀.fixingSubgroup → AlgEquiv.restrictNormalHom ↥F s = 1 := by
    refine ⟨F, hF, fun s hs => ?_⟩
    ext y
    rw [AlgEquiv.one_apply]
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs
    exact (AlgEquiv.restrictNormal_commutes s (↥F) y).trans (hs _ y.2)
  have hΛE'' : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F') f' g' (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
      ιE' κ ΛE' := hΛE'
  exact core (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) (M := M)
    (X := NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) (X' := NumberField.SUnits.sUnitsRep ℚ ↥F' Sℚ) S (AlgEquiv.restrictNormalHom ↥F) (AlgEquiv.restrictNormalHom ↥F') π hπ hπlev f g hfg hg f' g' ρR ρP hρf hρg
    ιE ιE' hιeq jE hjE κ hκeq hκ
    (NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective S hpS Sℚ hSℚ F hF f g hf hfg hg hB ιE hιE)
    hΛE hΛE'' a a' ha'

end S_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq
end P2MW
export P2MW.S_NumberField_SUnits_isGlobalBridge2_apply_inflation_eq (solution)
