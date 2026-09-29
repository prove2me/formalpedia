-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/5150612e-38a9-533e-9b61-cf9003b2d6ea

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_Dieudonne_ModpRealization
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_eq_algebraMap_sections_top
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

open TensorProduct TopologicalSpace

namespace C3Body

theorem globalScalars
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) (s : Γ(A, ⊤)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom f ⊤
    ∃ c : K, s = algebraMap K Γ(A, ⊤) c :=
  GoodReductionJacobian.AbelianSchemePropertyBundle.exists_eq_algebraMap_sections_top K f hA 𝒦 s

theorem eq_zero_of_one_tmul_eq_zero (K : Type u) [Field K] (S : Type u) [CommRing S] [Algebra K S] [Nontrivial S]
    (H : Type u) [AddCommGroup H] [Module K H] (h : H) (hh : (1 : S) ⊗ₜ[K] h = 0) : h = 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K S)
    (LinearMap.ker_eq_bot.mpr (algebraMap K S).injective)
  have hg1 : g 1 = 1 := by
    have := LinearMap.congr_fun hg 1
    simpa [Algebra.linearMap_apply] using this
  have key : (TensorProduct.lid K H) (TensorProduct.map g LinearMap.id ((1 : S) ⊗ₜ[K] h)) = h := by
    rw [TensorProduct.map_tmul, hg1, LinearMap.id_apply, TensorProduct.lid_tmul, one_smul]
  rw [hh, map_zero, map_zero] at key
  exact key.symm

theorem isAffineOpen_inter (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (𝒦 : A.OrderedAffineCover) {n : ℕ} (t : 𝒦.Idx n) :
    IsAffineOpen (𝒦.inter t) := by
  haveI : IsSeparated f := hA.proper.toIsSeparated
  haveI : IsSeparated (terminal.from A) := by rw [← terminal.comp_from f]; infer_instance
  haveI : IsAffineHom (pullback.diagonal (terminal.from A)) := inferInstance
  exact IsAffineOpen.iInf (fun j => 𝒦.isAffineOpen (t.1 j))

theorem exists_glue_sections {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    (S' : ∀ i, Γ(X, U i))
    (hagree : ∀ i j, (X.presheaf.map (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op).hom (S' i) =
      (X.presheaf.map (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op).hom (S' j)) :
    ∃ s : Γ(X, ⊤), ∀ i, (X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op).hom s = S' i := by
  obtain ⟨s, hs, -⟩ := TopCat.Sheaf.existsUnique_gluing' X.sheaf U ⊤ (fun i => homOfLE le_top)
    (by rw [hU]) S' (fun i j => hagree i j)
  exact ⟨s, hs⟩

theorem res_res {X : Scheme.{u}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (h₃ : W ≤ U) (s : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom s) =
      (X.presheaf.map (homOfLE h₃).op).hom s := by
  rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
  rfl

theorem exists_glue_of_forall_diff_eq_zero
    {A : Scheme.{u}} (N : A ⟶ A) (𝒦 : A.OrderedAffineCover)
    (S' : ∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ (𝒦.U i)))
    (hagree : ∀ t : 𝒦.Idx 1,
      (A.presheaf.map (homOfLE (show N ⁻¹ᵁ 𝒦.inter t ≤ N ⁻¹ᵁ 𝒦.U (t.1 0) from
        fun x hx => 𝒦.inter_le t 0 hx)).op).hom (S' (t.1 0)) =
      (A.presheaf.map (homOfLE (show N ⁻¹ᵁ 𝒦.inter t ≤ N ⁻¹ᵁ 𝒦.U (t.1 1) from
        fun x hx => 𝒦.inter_le t 1 hx)).op).hom (S' (t.1 1))) :
    ∃ s : Γ(A, ⊤), ∀ i, (A.presheaf.map (homOfLE (le_top : N ⁻¹ᵁ (𝒦.U i) ≤ ⊤)).op).hom s = S' i := by
  classical
  apply exists_glue_sections (fun i => N ⁻¹ᵁ (𝒦.U i))
  · rw [← Scheme.Hom.preimage_iSup, 𝒦.iSup_eq_top]; rfl
  ·

    have key : ∀ i j : 𝒦.ι, i < j →
        (A.presheaf.map (homOfLE (inf_le_left : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U i)).op).hom (S' i) =
        (A.presheaf.map (homOfLE (inf_le_right : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U j)).op).hom (S' j) := by
      intro i j hij
      let t : 𝒦.Idx 1 := ⟨![i, j], Fin.strictMono_iff_lt_succ.mpr (fun k => by fin_cases k; simpa using hij)⟩
      have ht0 : t.1 0 = i := rfl
      have ht1 : t.1 1 = j := rfl
      have hle : 𝒦.U i ⊓ 𝒦.U j ≤ 𝒦.inter t :=
        le_iInf fun k => by fin_cases k <;> [exact inf_le_left; exact inf_le_right]
      have hW : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.inter t := fun x hx => hle ⟨hx.1, hx.2⟩
      have h := congrArg (fun z => (A.presheaf.map (homOfLE hW).op).hom z) (hagree t)
      have l := res_res (X := A) (show N ⁻¹ᵁ 𝒦.inter t ≤ N ⁻¹ᵁ 𝒦.U (t.1 0) from fun x hx => 𝒦.inter_le t 0 hx) hW
        (inf_le_left : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U (t.1 0)) (S' (t.1 0))
      have r := res_res (X := A) (show N ⁻¹ᵁ 𝒦.inter t ≤ N ⁻¹ᵁ 𝒦.U (t.1 1) from fun x hx => 𝒦.inter_le t 1 hx) hW
        (inf_le_right : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U (t.1 1)) (S' (t.1 1))
      exact l.symm.trans (h.trans r)
    intro i j
    rcases lt_trichotomy i j with hij | rfl | hji
    · exact key i j hij
    · rfl
    · have h := key j i hji

      have e : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U j ⊓ N ⁻¹ᵁ 𝒦.U i :=
        (inf_comm (N ⁻¹ᵁ 𝒦.U i) (N ⁻¹ᵁ 𝒦.U j)).le
      have h' := congrArg (fun z => (A.presheaf.map (homOfLE e).op).hom z) h
      have l := res_res (X := A) (inf_le_left : N ⁻¹ᵁ 𝒦.U j ⊓ N ⁻¹ᵁ 𝒦.U i ≤ N ⁻¹ᵁ 𝒦.U j) e
        (inf_le_right : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U j) (S' j)
      have r := res_res (X := A) (inf_le_right : N ⁻¹ᵁ 𝒦.U j ⊓ N ⁻¹ᵁ 𝒦.U i ≤ N ⁻¹ᵁ 𝒦.U i) e
        (inf_le_left : N ⁻¹ᵁ 𝒦.U i ⊓ N ⁻¹ᵁ 𝒦.U j ≤ N ⁻¹ᵁ 𝒦.U i) (S' i)
      exact (l.symm.trans (h'.trans r)).symm

end C3Body

set_option maxHeartbeats 4000000 in
theorem solution
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (hA : AbelianSchemePropertyBundle K f) (N : A ⟶ A) (hN : N ≫ f = f)
    (H : Type u) [CommRing H] [HopfAlgebra K H]
    (hdata : letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
      ∃ ρ : (∀ U : A.affineOpens, Γ(A, N ⁻¹ᵁ (U : A.Opens)) →ₐ[K] Γ(A, N ⁻¹ᵁ (U : A.Opens)) ⊗[K] H),
        (∀ (U U' : A.affineOpens) (hle : (N ⁻¹ᵁ (U' : A.Opens)) ≤ N ⁻¹ᵁ (U : A.Opens))
            (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
            Algebra.TensorProduct.map (Scheme.TwoAffineOpenCover.restrictAlgHom f hle) (AlgHom.id K H) (ρ U s) =
              ρ U' ((A.presheaf.map (homOfLE hle).op).hom s)) ∧
        (∀ U : A.affineOpens, Function.Injective (N.app (U : A.Opens)).hom) ∧
        (∀ (U : A.affineOpens) (r : Γ(A, (U : A.Opens))),
            ρ U ((N.app (U : A.Opens)).hom r) = (N.app (U : A.Opens)).hom r ⊗ₜ[K] (1 : H)) ∧
        (∀ (U : A.affineOpens) (s : Γ(A, N ⁻¹ᵁ (U : A.Opens))),
            ρ U s = s ⊗ₜ[K] (1 : H) → s ∈ Set.range (N.app (U : A.Opens)).hom) ∧
        (∀ (U : A.affineOpens) (h : H), h ∈ primitives K H →
            ∃ s : Γ(A, N ⁻¹ᵁ (U : A.Opens)), ρ U s = s ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ (U : A.Opens))) ⊗ₜ[K] h))
    (𝒦 : A.OrderedAffineCover) :
    ∃ θ : ↥(primitives K H) →ₗ[K] (OModulePresheaf.unit f).HSucc 𝒦 0, Function.Injective θ := by
  classical
  letI instK : ∀ V : A.Opens, Algebra K Γ(A, V) := fun V => Scheme.TwoAffineOpenCover.algebraOfHom f V
  obtain ⟨ρ, hnat, hinj, hρN, hcoinv, hlift⟩ := hdata

  let Uo : 𝒦.ι → A.Opens := fun i => 𝒦.U i
  let Ua : 𝒦.ι → A.affineOpens := fun i => ⟨𝒦.U i, 𝒦.isAffineOpen i⟩
  let Wa : ∀ {n : ℕ}, 𝒦.Idx n → A.affineOpens := fun t => ⟨𝒦.inter t, C3Body.isAffineOpen_inter K f hA 𝒦 t⟩

  have hpre : ∀ {V V' : A.Opens}, V' ≤ V → N ⁻¹ᵁ V' ≤ N ⁻¹ᵁ V := fun h x hx => h hx
  let resN : ∀ {V V' : A.Opens}, V' ≤ V → Γ(A, N ⁻¹ᵁ V) → Γ(A, N ⁻¹ᵁ V') :=
    fun h => (A.presheaf.map (homOfLE (hpre h)).op).hom

  let IsLift : H → (∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ (Uo i))) → Prop :=
    fun h S => ∀ i, ρ (Ua i) (S i) = S i ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ (Uo i))) ⊗ₜ[K] h
  let diff : (∀ i : 𝒦.ι, Γ(A, N ⁻¹ᵁ (Uo i))) → ∀ t : 𝒦.Idx 1, Γ(A, N ⁻¹ᵁ 𝒦.inter t) :=
    fun S t => resN (𝒦.inter_le t 0) (S (t.1 0)) - resN (𝒦.inter_le t 1) (S (t.1 1))

  have hNalg : ∀ (V : A.Opens) (a : K), (N.app V).hom (algebraMap K Γ(A, V) a) = algebraMap K Γ(A, N ⁻¹ᵁ V) a := by
    intro V a
    change (N.app V).hom ((f.appLE ⊤ V le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom a)) =
      (f.appLE ⊤ (N ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (.of K)).inv.hom a)
    rw [← CommRingCat.comp_apply]
    congr 2
    rw [Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    have key : ∀ (g : A ⟶ Spec (CommRingCat.of K)) (hg : g = f) (e : N ⁻¹ᵁ V ≤ g ⁻¹ᵁ ⊤) (e' : N ⁻¹ᵁ V ≤ f ⁻¹ᵁ ⊤),
        g.appLE ⊤ (N ⁻¹ᵁ V) e = f.appLE ⊤ (N ⁻¹ᵁ V) e' := by
      rintro g rfl e e'; rfl
    exact key (N ≫ f) hN _ _
  have hNsmul : ∀ (V : A.Opens) (a : K) (c : Γ(A, V)), (N.app V).hom (a • c) = a • (N.app V).hom c := by
    intro V a c
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hNalg]
  have hres_smul : ∀ {V V' : A.Opens} (h : V' ≤ V) (a : K) (s : Γ(A, N ⁻¹ᵁ V)), resN h (a • s) = a • resN h s :=
    fun h a s => map_smul (Scheme.TwoAffineOpenCover.restrictAlgHom f (hpre h)) a s
  have hdiff_add : ∀ (S S' : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i))) (t : 𝒦.Idx 1), diff (S + S') t = diff S t + diff S' t := by
    intro S S' t
    simp only [diff, resN, Pi.add_apply, map_add]
    abel
  have hdiff_smul : ∀ (a : K) (S : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i))) (t : 𝒦.Idx 1), diff (a • S) t = a • diff S t := by
    intro a S t
    simp only [diff, Pi.smul_apply, hres_smul, smul_sub]

  have hAB : ∀ (h : H) (S : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i))), IsLift h S →
      ∀ t : 𝒦.Idx 1, ∃! c : Γ(A, 𝒦.inter t), (N.app (𝒦.inter t)).hom c = diff S t := by
    intro h S hS t
    have key : ∀ j : Fin 2, ρ (Wa t) (resN (𝒦.inter_le t j) (S (t.1 j))) =
        resN (𝒦.inter_le t j) (S (t.1 j)) ⊗ₜ[K] (1 : H) + (1 : Γ(A, N ⁻¹ᵁ 𝒦.inter t)) ⊗ₜ[K] h := by
      intro j
      have hn := hnat (Ua (t.1 j)) (Wa t) (hpre (𝒦.inter_le t j)) (S (t.1 j))
      change _ = ρ (Wa t) (resN (𝒦.inter_le t j) (S (t.1 j))) at hn
      rw [← hn, hS (t.1 j), map_add, Algebra.TensorProduct.map_tmul, Algebra.TensorProduct.map_tmul, map_one,
        AlgHom.id_apply, map_one]
      rfl
    have hρ : ρ (Wa t) (diff S t) = diff S t ⊗ₜ[K] (1 : H) := by
      change ρ (Wa t) (resN (𝒦.inter_le t 0) (S (t.1 0)) - resN (𝒦.inter_le t 1) (S (t.1 1))) =
        (resN (𝒦.inter_le t 0) (S (t.1 0)) - resN (𝒦.inter_le t 1) (S (t.1 1))) ⊗ₜ[K] (1 : H)
      rw [map_sub, key 0, key 1, TensorProduct.sub_tmul]
      abel
    obtain ⟨c, hc⟩ := hcoinv (Wa t) (diff S t) hρ
    exact ⟨c, hc, fun c' hc' => hinj (Wa t) (hc'.trans hc.symm)⟩

  let coc : ∀ (h : H) (S : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i))), IsLift h S → (OModulePresheaf.unit f).cochain 𝒦 1 :=
    fun h S hS t => (hAB h S hS t).exists.choose
  have hcoc : ∀ (h : H) (S) (hS : IsLift h S) (t : 𝒦.Idx 1),
      (N.app (𝒦.inter t)).hom (coc h S hS t) = diff S t :=
    fun h S hS t => (hAB h S hS t).exists.choose_spec

  have hC : ∀ (h : H) (S) (hS : IsLift h S), (OModulePresheaf.unit f).d 𝒦 1 (coc h S hS) = 0 := by
    intro h S hS

    have hrr : ∀ {V₁ V₂ V₃ : A.Opens} (h₁ : V₂ ≤ V₁) (h₂ : V₃ ≤ V₂) (s : Γ(A, N ⁻¹ᵁ V₁)),
        resN h₂ (resN h₁ s) = resN (h₂.trans h₁) s := by
      intro V₁ V₂ V₃ h₁ h₂ s
      change (A.presheaf.map (homOfLE (hpre h₁)).op ≫ A.presheaf.map (homOfLE (hpre h₂)).op).hom s = _
      rw [← A.presheaf.map_comp]
      rfl

    have hNres : ∀ {V V' : A.Opens} (hle : V' ≤ V) (c : Γ(A, V)),
        (N.app V').hom ((A.presheaf.map (homOfLE hle).op).hom c) = resN hle ((N.app V).hom c) := by
      intro V V' hle c
      change (A.presheaf.map (homOfLE hle).op ≫ N.app V').hom c = (N.app V ≫ A.presheaf.map (homOfLE (hpre hle)).op).hom c
      rw [N.naturality (homOfLE hle).op]
      rfl
    have hsubN : ∀ {V V' : A.Opens} (hle : V' ≤ V) (a b : Γ(A, N ⁻¹ᵁ V)),
        resN hle (a - b) = resN hle a - resN hle b := fun hle a b => map_sub _ a b
    funext u
    let r : Fin (1 + 2) → Γ(A, N ⁻¹ᵁ 𝒦.inter u) := fun i => resN (𝒦.inter_le u i) (S (u.1 i))
    have hterm : ∀ j : Fin 3, (N.app (𝒦.inter u)).hom
        ((A.presheaf.map (homOfLE (𝒦.inter_le_inter_face u j)).op).hom (coc h S hS (𝒦.face u j))) =
        r (j.succAbove 0) - r (j.succAbove 1) := by
      intro j
      rw [hNres (𝒦.inter_le_inter_face u j), hcoc h S hS (𝒦.face u j)]
      change resN (𝒦.inter_le_inter_face u j) (resN (𝒦.inter_le (𝒦.face u j) 0) (S ((𝒦.face u j).1 0)) -
          resN (𝒦.inter_le (𝒦.face u j) 1) (S ((𝒦.face u j).1 1))) = _
      rw [hsubN (𝒦.inter_le_inter_face u j), hrr (𝒦.inter_le (𝒦.face u j) 0) (𝒦.inter_le_inter_face u j),
        hrr (𝒦.inter_le (𝒦.face u j) 1) (𝒦.inter_le_inter_face u j)]
      rfl
    rw [OModulePresheaf.d_apply, Fin.sum_univ_three]
    simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one, neg_one_sq, one_smul, neg_one_smul]
    apply hinj (Wa u)
    change (N.app (𝒦.inter u)).hom
        ((A.presheaf.map (homOfLE (𝒦.inter_le_inter_face u 0)).op).hom (coc h S hS (𝒦.face u 0)) +
          -(A.presheaf.map (homOfLE (𝒦.inter_le_inter_face u 1)).op).hom (coc h S hS (𝒦.face u 1)) +
          (A.presheaf.map (homOfLE (𝒦.inter_le_inter_face u 2)).op).hom (coc h S hS (𝒦.face u 2))) =
      (N.app (𝒦.inter u)).hom 0
    rw [map_add, map_add, map_neg, map_zero, hterm 0, hterm 1, hterm 2]
    have h00 : (0 : Fin (1 + 2)).succAbove (0 : Fin (1 + 1)) = 1 := by decide
    have h01 : (0 : Fin (1 + 2)).succAbove (1 : Fin (1 + 1)) = 2 := by decide
    have h10 : (1 : Fin (1 + 2)).succAbove (0 : Fin (1 + 1)) = 0 := by decide
    have h11 : (1 : Fin (1 + 2)).succAbove (1 : Fin (1 + 1)) = 2 := by decide
    have h20 : (2 : Fin (1 + 2)).succAbove (0 : Fin (1 + 1)) = 0 := by decide
    have h21 : (2 : Fin (1 + 2)).succAbove (1 : Fin (1 + 1)) = 1 := by decide
    simp only [h00, h01, h10, h11, h20, h21]
    abel

  have hobj_add : ∀ (t : 𝒦.Idx 1) (x y : (OModulePresheaf.unit f).obj (𝒦.inter t)),
      (N.app (𝒦.inter t)).hom (x + y) = (N.app (𝒦.inter t)).hom x + (N.app (𝒦.inter t)).hom y :=
    fun t x y => map_add ((N.app (𝒦.inter t)).hom) x y
  have hobj_smul : ∀ (t : 𝒦.Idx 1) (a : K) (x : (OModulePresheaf.unit f).obj (𝒦.inter t)),
      (N.app (𝒦.inter t)).hom (a • x) = a • (N.app (𝒦.inter t)).hom x :=
    fun t a x => hNsmul (𝒦.inter t) a x
  have hD_add : ∀ (h h' : H) (S S') (hS : IsLift h S) (hS' : IsLift h' S') (hSS' : IsLift (h + h') (S + S')),
      coc (h + h') (S + S') hSS' = coc h S hS + coc h' S' hS' := by
    intro h h' S S' hS hS' hSS'
    funext t
    refine (hAB _ _ hSS' t).unique (hcoc _ _ hSS' t) ?_
    change (N.app (𝒦.inter t)).hom (coc h S hS t + coc h' S' hS' t) = diff (S + S') t
    rw [hobj_add, hcoc h S hS t, hcoc h' S' hS' t, hdiff_add]
  have hD_smul : ∀ (a : K) (h : H) (S) (hS : IsLift h S) (haS : IsLift (a • h) (a • S)),
      coc (a • h) (a • S) haS = a • coc h S hS := by
    intro a h S hS haS
    funext t
    refine (hAB _ _ haS t).unique (hcoc _ _ haS t) ?_
    change (N.app (𝒦.inter t)).hom (a • coc h S hS t) = diff (a • S) t
    rw [hobj_smul, hcoc h S hS t, hdiff_smul]

  have hobj_sub : ∀ (t : 𝒦.Idx 1) (x y : (OModulePresheaf.unit f).obj (𝒦.inter t)),
      (N.app (𝒦.inter t)).hom (x - y) = (N.app (𝒦.inter t)).hom x - (N.app (𝒦.inter t)).hom y :=
    fun t x y => map_sub ((N.app (𝒦.inter t)).hom) x y
  have hNres : ∀ {V V' : A.Opens} (hle : V' ≤ V) (x : Γ(A, V)),
      (N.app V').hom ((A.presheaf.map (homOfLE hle).op).hom x) = resN hle ((N.app V).hom x) := by
    intro V V' hle x
    have := congrArg (fun φ => φ.hom x) (N.naturality (homOfLE hle).op)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at this
    exact this
  have hresN_comp : ∀ {V V' V'' : A.Opens} (h1 : V' ≤ V) (h2 : V'' ≤ V') (x : Γ(A, N ⁻¹ᵁ V)),
      resN h2 (resN h1 x) = resN (h2.trans h1) x := by
    intro V V' V'' h1 h2 x
    change (A.presheaf.map (homOfLE (hpre h1)).op ≫ A.presheaf.map (homOfLE (hpre h2)).op).hom x = _
    rw [← A.presheaf.map_comp]
    rfl
  have hres_comp : ∀ {U V W : A.Opens} (h1 : V ≤ U) (h2 : W ≤ V) (x : Γ(A, U)),
      (A.presheaf.map (homOfLE h2).op).hom ((A.presheaf.map (homOfLE h1).op).hom x) =
        (A.presheaf.map (homOfLE (h2.trans h1)).op).hom x := by
    intro U V W h1 h2 x
    rw [← CommRingCat.comp_apply, ← A.presheaf.map_comp]
    rfl
  have hd0 : ∀ (b : (OModulePresheaf.unit f).cochain 𝒦 0) (t : 𝒦.Idx 1),
      (OModulePresheaf.unit f).d 𝒦 0 b t =
        (OModulePresheaf.unit f).res (𝒦.inter_le_inter_face t 0) (b (𝒦.face t 0)) -
          (OModulePresheaf.unit f).res (𝒦.inter_le_inter_face t 1) (b (𝒦.face t 1)) := by
    intro b t
    rw [OModulePresheaf.d_apply, Fin.sum_univ_two]
    simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_smul, sub_eq_add_neg]
  have hface10 : ∀ t : 𝒦.Idx 1, (𝒦.face t 0).1 0 = t.1 1 := fun t => by
    rw [𝒦.face_val]; rfl
  have hface11 : ∀ t : 𝒦.Idx 1, (𝒦.face t 1).1 0 = t.1 0 := fun t => by
    rw [𝒦.face_val]; rfl

  have hE : ∀ (h : H) (S S') (hS : IsLift h S) (hS' : IsLift h S'),
      coc h S' hS' - coc h S hS ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0) := by
    intro h S S' hS hS'
    have hci : ∀ i, ∃ b : Γ(A, Uo i), (N.app (Uo i)).hom b = S' i - S i := by
      intro i
      obtain ⟨b, hb⟩ := hcoinv (Ua i) (S' i - S i) (by
        rw [map_sub, hS i, hS' i, TensorProduct.sub_tmul]; abel)
      exact ⟨b, hb⟩
    choose bt hbt using hci
    let b : (OModulePresheaf.unit f).cochain 𝒦 0 := fun t0 => (OModulePresheaf.unit f).res (𝒦.inter_le t0 0) (bt (t0.1 0))
    refine ⟨-b, ?_⟩
    funext t
    apply hinj (Wa t)
    change (N.app (𝒦.inter t)).hom ((OModulePresheaf.unit f).d 𝒦 0 (-b) t) =
      (N.app (𝒦.inter t)).hom (coc h S' hS' t - coc h S hS t)
    rw [hobj_sub, hcoc h S' hS' t, hcoc h S hS t, map_neg, Pi.neg_apply, hd0]
    change (N.app (𝒦.inter t)).hom (-((A.presheaf.map (homOfLE (𝒦.inter_le_inter_face t 0)).op).hom
        ((A.presheaf.map (homOfLE (𝒦.inter_le (𝒦.face t 0) 0)).op).hom (bt ((𝒦.face t 0).1 0))) -
      (A.presheaf.map (homOfLE (𝒦.inter_le_inter_face t 1)).op).hom
        ((A.presheaf.map (homOfLE (𝒦.inter_le (𝒦.face t 1) 0)).op).hom (bt ((𝒦.face t 1).1 0))))) = diff S' t - diff S t
    rw [map_neg, map_sub, hNres, hNres, hNres, hNres,
      hresN_comp (𝒦.inter_le (𝒦.face t 0) 0) (𝒦.inter_le_inter_face t 0),
      hresN_comp (𝒦.inter_le (𝒦.face t 1) 0) (𝒦.inter_le_inter_face t 1), hbt, hbt]

    have hcongr : ∀ (F : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i))) (i j : 𝒦.ι) (e : i = j) (h1 : 𝒦.inter t ≤ Uo i) (h2 : 𝒦.inter t ≤ Uo j),
        resN h1 (F i) = resN h2 (F j) := by
      intro F i j e h1 h2; subst e; rfl
    have e1 : resN ((𝒦.inter_le_inter_face t 0).trans (𝒦.inter_le (𝒦.face t 0) 0)) (S' ((𝒦.face t 0).1 0) - S ((𝒦.face t 0).1 0)) =
        resN (𝒦.inter_le t 1) (S' (t.1 1) - S (t.1 1)) :=
      hcongr (fun i => S' i - S i) _ _ (hface10 t) ((𝒦.inter_le_inter_face t 0).trans (𝒦.inter_le (𝒦.face t 0) 0)) (𝒦.inter_le t 1)
    have e2 : resN ((𝒦.inter_le_inter_face t 1).trans (𝒦.inter_le (𝒦.face t 1) 0)) (S' ((𝒦.face t 1).1 0) - S ((𝒦.face t 1).1 0)) =
        resN (𝒦.inter_le t 0) (S' (t.1 0) - S (t.1 0)) :=
      hcongr (fun i => S' i - S i) _ _ (hface11 t) ((𝒦.inter_le_inter_face t 1).trans (𝒦.inter_le (𝒦.face t 1) 0)) (𝒦.inter_le t 0)
    rw [e1, e2]
    simp only [diff, resN, map_sub]
    abel

  have hF : ∀ (h : H) (S) (hS : IsLift h S),
      coc h S hS ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 0) → h = 0 := by
    intro h S hS hmem
    obtain ⟨b, hb⟩ := hmem

    have hsm : ∀ i : 𝒦.ι, StrictMono (fun _ : Fin 1 => i) := fun i a b hab =>
      absurd hab (by rw [Fin.fin_one_eq_zero a, Fin.fin_one_eq_zero b]; exact lt_irrefl _)
    let idx0 : 𝒦.ι → 𝒦.Idx 0 := fun i => ⟨fun _ => i, hsm i⟩
    have hUle : ∀ i, Uo i ≤ 𝒦.inter (idx0 i) := fun i => le_iInf fun _ => le_rfl
    let bt : ∀ i, Γ(A, Uo i) := fun i => (OModulePresheaf.unit f).res (hUle i) (b (idx0 i))
    let T : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i)) := fun i => (N.app (Uo i)).hom (bt i)
    let S' : ∀ i, Γ(A, N ⁻¹ᵁ (Uo i)) := S + T
    have hS' : IsLift h S' := by
      intro i
      change ρ (Ua i) (S i + (N.app (Uo i)).hom (bt i)) = (S i + (N.app (Uo i)).hom (bt i)) ⊗ₜ[K] (1 : H) + 1 ⊗ₜ[K] h
      rw [map_add, hS i, hρN (Ua i) (bt i), TensorProduct.add_tmul]
      abel

    have hface0 : ∀ t : 𝒦.Idx 1, 𝒦.face t 0 = idx0 (t.1 1) := fun t =>
      Subtype.ext (funext fun j => by rw [𝒦.face_val, Fin.fin_one_eq_zero j]; rfl)
    have hface1 : ∀ t : 𝒦.Idx 1, 𝒦.face t 1 = idx0 (t.1 0) := fun t =>
      Subtype.ext (funext fun j => by rw [𝒦.face_val, Fin.fin_one_eq_zero j]; rfl)
    have hbcongr : ∀ (t : 𝒦.Idx 1) (u v : 𝒦.Idx 0) (e : u = v) (h1 : 𝒦.inter t ≤ 𝒦.inter u) (h2 : 𝒦.inter t ≤ 𝒦.inter v),
        (OModulePresheaf.unit f).res h1 (b u) = (OModulePresheaf.unit f).res h2 (b v) := by
      intro t u v e h1 h2; subst e; rfl

    have hT : ∀ (t : 𝒦.Idx 1) (k : Fin 2), resN (𝒦.inter_le t k) (T (t.1 k)) =
        (N.app (𝒦.inter t)).hom ((OModulePresheaf.unit f).res ((𝒦.inter_le t k).trans (hUle (t.1 k))) (b (idx0 (t.1 k)))) := by
      intro t k
      change resN (𝒦.inter_le t k) ((N.app (Uo (t.1 k))).hom ((A.presheaf.map (homOfLE (hUle (t.1 k))).op).hom (b (idx0 (t.1 k))))) =
        (N.app (𝒦.inter t)).hom ((A.presheaf.map (homOfLE ((𝒦.inter_le t k).trans (hUle (t.1 k)))).op).hom (b (idx0 (t.1 k))))
      rw [← hNres (𝒦.inter_le t k) ((A.presheaf.map (homOfLE (hUle (t.1 k))).op).hom (b (idx0 (t.1 k)))), hres_comp]

    have hdiff0 : ∀ t : 𝒦.Idx 1, diff S' t = 0 := by
      intro t
      have hct := congrArg (fun c => (N.app (𝒦.inter t)).hom (c t)) hb
      rw [hcoc h S hS t, hd0,
        hbcongr t _ _ (hface0 t) (𝒦.inter_le_inter_face t 0) ((𝒦.inter_le t 1).trans (hUle (t.1 1))),
        hbcongr t _ _ (hface1 t) (𝒦.inter_le_inter_face t 1) ((𝒦.inter_le t 0).trans (hUle (t.1 0))),
        hobj_sub] at hct
      change diff (S + T) t = 0
      rw [hdiff_add, ← hct]
      change _ + (resN (𝒦.inter_le t 0) (T (t.1 0)) - resN (𝒦.inter_le t 1) (T (t.1 1))) = 0
      rw [hT t 0, hT t 1]
      abel

    obtain ⟨s, hs⟩ := C3Body.exists_glue_of_forall_diff_eq_zero N 𝒦 S' (fun t => sub_eq_zero.mp (hdiff0 t))

    obtain ⟨lam, hlam⟩ := C3Body.globalScalars K f hA 𝒦 s
    have hS'lam : ∀ i, S' i = algebraMap K Γ(A, N ⁻¹ᵁ (Uo i)) lam := by
      intro i
      rw [← hs i, hlam]
      exact (Scheme.TwoAffineOpenCover.restrictAlgHom f (le_top : N ⁻¹ᵁ (Uo i) ≤ ⊤)).commutes lam

    obtain ⟨x⟩ : Nonempty A := by
      obtain ⟨x, hx⟩ := (hA.connectedFibres (IsLocalRing.closedPoint K)).nonempty
      exact ⟨x⟩
    have hxtop : x ∈ (⨆ i, N ⁻¹ᵁ (Uo i) : A.Opens) := by
      rw [← Scheme.Hom.preimage_iSup, 𝒦.iSup_eq_top]; trivial
    obtain ⟨i, hxi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxtop
    haveI : Nontrivial Γ(A, N ⁻¹ᵁ (Uo i)) :=
      (A.presheaf.germ (N ⁻¹ᵁ (Uo i)) x hxi).hom.domain_nontrivial

    have h1 := hS' i
    rw [hS'lam i, AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply] at h1
    have h2 : (1 : Γ(A, N ⁻¹ᵁ (Uo i))) ⊗ₜ[K] h = 0 := by
      have := h1
      rw [eq_comm, add_eq_left] at this
      exact this
    exact C3Body.eq_zero_of_one_tmul_eq_zero K (Γ(A, N ⁻¹ᵁ (Uo i))) H h h2

  have hexS : ∀ h : ↥(primitives K H), ∃ S, IsLift (h : H) S :=
    fun h => ⟨fun i => (hlift (Ua i) h h.2).choose, fun i => (hlift (Ua i) h h.2).choose_spec⟩
  let S₀ : ∀ h : ↥(primitives K H), (∀ i, Γ(A, N ⁻¹ᵁ (Uo i))) := fun h => (hexS h).choose
  have hS₀ : ∀ h : ↥(primitives K H), IsLift (h : H) (S₀ h) := fun h => (hexS h).choose_spec
  have hLift_add : ∀ (h h' : H) (S S'), IsLift h S → IsLift h' S' → IsLift (h + h') (S + S') := by
    intro h h' S S' hS hS' i
    simp only [Pi.add_apply, map_add, hS i, hS' i, TensorProduct.tmul_add, TensorProduct.add_tmul]
    abel
  have hLift_smul : ∀ (a : K) (h : H) (S), IsLift h S → IsLift (a • h) (a • S) := by
    intro a h S hS i
    simp only [Pi.smul_apply, map_smul, hS i, smul_add, TensorProduct.tmul_smul, TensorProduct.smul_tmul']

  let cls : ∀ (h : H) (S) (hS : IsLift h S), (OModulePresheaf.unit f).HSucc 𝒦 0 :=
    fun h S hS => Submodule.Quotient.mk ⟨coc h S hS, LinearMap.mem_ker.mpr (hC h S hS)⟩
  have hcls_indep : ∀ (h : H) (S S') (hS : IsLift h S) (hS' : IsLift h S'), cls h S hS = cls h S' hS' := by
    intro h S S' hS hS'
    rw [eq_comm, ← sub_eq_zero]
    change Submodule.Quotient.mk ((⟨coc h S' hS', LinearMap.mem_ker.mpr (hC h S' hS')⟩ : LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 1)) -
        ⟨coc h S hS, LinearMap.mem_ker.mpr (hC h S hS)⟩) = 0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hE h S S' hS hS'
  let θfun : ↥(primitives K H) → (OModulePresheaf.unit f).HSucc 𝒦 0 := fun h => cls h (S₀ h) (hS₀ h)
  have hθ_add : ∀ h h' : ↥(primitives K H), θfun (h + h') = θfun h + θfun h' := by
    intro h h'
    change cls _ (S₀ (h + h')) (hS₀ (h + h')) = cls _ (S₀ h) (hS₀ h) + cls _ (S₀ h') (hS₀ h')
    rw [hcls_indep (h + h' : ↥(primitives K H)) (S₀ (h + h')) (S₀ h + S₀ h') (hS₀ (h + h'))
      (hLift_add _ _ _ _ (hS₀ h) (hS₀ h'))]
    change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact hD_add _ _ _ _ (hS₀ h) (hS₀ h') (hLift_add _ _ _ _ (hS₀ h) (hS₀ h'))
  have hθ_smul : ∀ (a : K) (h : ↥(primitives K H)), θfun (a • h) = a • θfun h := by
    intro a h
    change cls _ (S₀ (a • h)) (hS₀ (a • h)) = a • cls _ (S₀ h) (hS₀ h)
    rw [hcls_indep (a • h : ↥(primitives K H)) (S₀ (a • h)) (a • S₀ h) (hS₀ (a • h)) (hLift_smul _ _ _ (hS₀ h))]
    change Submodule.Quotient.mk _ = a • Submodule.Quotient.mk _
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact hD_smul _ _ _ (hS₀ h) (hLift_smul _ _ _ (hS₀ h))
  let θ : ↥(primitives K H) →ₗ[K] (OModulePresheaf.unit f).HSucc 𝒦 0 :=
    { toFun := θfun, map_add' := hθ_add, map_smul' := hθ_smul }
  refine ⟨θ, ?_⟩
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro h hh
  rw [LinearMap.mem_ker] at hh
  change cls _ (S₀ h) (hS₀ h) = 0 at hh
  change Submodule.Quotient.mk _ = 0 at hh
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at hh
  exact Subtype.ext (hF _ _ (hS₀ h) hh)

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_linearMap_primitives_HSucc_unit_injective_of_forall_affineOpens_coaction (solution)
