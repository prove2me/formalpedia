-- Prove2me | solution 1 for LanglandsTunnell.exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/5f34e5cd-4a21-5343-b709-a20415eada30

import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Theorems.Thm_AutomorphicForm_continuous_and_hasCompactSupport_of_isFactorizableTestFn
import Theorems.Thm_AutomorphicForm_continuous_unipotentGL2
import Theorems.Thm_AutomorphicForm_IsCuspidalFn_add
import Theorems.Thm_AutomorphicForm_IsCuspidalFn_smul
import Theorems.Thm_HeckeIntegralSeam_heckeCosetSum_eq_of_isHeckeCosetSystem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup

set_option autoImplicit false

open IsDedekindDomain NumberField
open NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel
open AutomorphicForm.CuspidalConstituent
open FLT.SmoothVectors
open MeasureTheory

noncomputable section

section LinearAlgebra

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem map_mem_finsetSup_of_forall {T : V → V} {M : Submodule ℂ V} (hT0 : T 0 = 0)
    (hTadd : ∀ x y : V, x ∈ M → y ∈ M → T (x + y) = T x + T y)
    (s : Finset (Submodule ℂ V)) (hle : ∀ W ∈ s, W ≤ M) (hstab : ∀ W ∈ s, ∀ x ∈ W, T x ∈ W) :
    ∀ x ∈ s.sup id, T x ∈ s.sup id := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro x hx
    rw [Finset.sup_empty, Submodule.mem_bot] at hx ⊢
    rw [hx, hT0]
  | insert W s hW ih =>
    intro x hx
    rw [Finset.sup_insert] at hx ⊢
    have hle' : ∀ W' ∈ s, W' ≤ M := fun W' hW' => hle W' (Finset.mem_insert_of_mem hW')
    have hstab' : ∀ W' ∈ s, ∀ y ∈ W', T y ∈ W' :=
      fun W' hW' => hstab W' (Finset.mem_insert_of_mem hW')
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hx
    have hyM : y ∈ M := hle W (Finset.mem_insert_self W s) hy
    have hsM : s.sup id ≤ M := Finset.sup_le fun W' hW' => hle' W' hW'
    rw [hTadd y z hyM (hsM hz)]
    exact Submodule.add_mem_sup (hstab W (Finset.mem_insert_self W s) y hy) (ih hle' hstab' z hz)

private theorem map_eq_smul_of_inf_eq_bot {A B : Submodule ℂ V} (hAB : A ⊓ B = ⊥) {a b : V}
    (ha : a ∈ A) (hb : b ∈ B) {T : V → V} (hTa : T a ∈ A) (hTb : T b ∈ B)
    (hTadd : T (a + b) = T a + T b) {c : ℂ} (hT : T (a + b) = c • (a + b)) : T a = c • a := by
  have h : T a + T b = c • a + c • b := by rw [← hTadd, hT, smul_add]
  have hmem : T a - c • a ∈ A ⊓ B := by
    refine ⟨A.sub_mem hTa (A.smul_mem c ha), ?_⟩
    have h' : T a - c • a = c • b - T b := by
      rw [sub_eq_sub_iff_add_eq_add]
      exact h.trans (add_comm _ _)
    rw [h']
    exact B.sub_mem (B.smul_mem c hb) hTb
  rw [hAB, Submodule.mem_bot] at hmem
  exact sub_eq_zero.mp hmem

end LinearAlgebra

section KFinite

private theorem rightTranslate_one_eq (F : Type) [Field F] [NumberField F]
    (φ : AdelicGL2 (𝓞 F) F → ℂ) : rightTranslate F 1 φ = φ :=
  funext fun x => by rw [rightTranslate_apply, mul_one]

private theorem continuous_of_mem_cuspKFinite (F : Type) [Field F] [NumberField F]
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule F pins ξ) : Continuous φ := by
  refine Submodule.span_induction (p := fun φ _ => Continuous φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨-, hc, -⟩
    exact hc
  · exact continuous_zero
  · exact fun _ _ _ _ hu hw => hu.add hw
  · exact fun c _ _ hu => hu.const_smul c

private theorem automorphicFnAt_add_aux (F : Type) [Field F] [NumberField F]
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsAutomorphicFnAt F pins ξ φ) (hψ : IsAutomorphicFnAt F pins ξ ψ) :
    IsAutomorphicFnAt F pins ξ (φ + ψ) := by
  letI := pins.mS
  have hφ' := (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ).mp hφ
  have hψ' := (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D ψ).mp hψ
  refine (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D (φ + ψ)).mpr ⟨⟨?_, ?_⟩, hφ'.2.add hψ'.2⟩
  · intro γ g
    simp only [Pi.add_apply, hφ'.1.left_invariant γ g, hψ'.1.left_invariant γ g]
  · intro z g
    simp only [Pi.add_apply, hφ'.1.central_transform z g, hψ'.1.central_transform z g]
    ring

private theorem automorphicFnAt_smul_aux (F : Type) [Field F] [NumberField F]
    {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : IsAutomorphicFnAt F pins ξ φ) (c : ℂ) : IsAutomorphicFnAt F pins ξ (c • φ) := by
  letI := pins.mS
  have hφ' := (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D φ).mp hφ
  refine (lsXiMemberAt_iff (𝓞 F) F pins.μ pins.Z ξ pins.D (c • φ)).mpr
    ⟨⟨?_, ?_⟩, hφ'.2.const_smul c⟩
  · intro γ g
    simp only [Pi.smul_apply, smul_eq_mul, hφ'.1.left_invariant γ g]
  · intro z g
    simp only [Pi.smul_apply, smul_eq_mul, hφ'.1.central_transform z g]
    ring

private theorem kfSmooth_add_aux (F : Type) [Field F] [NumberField F]
    {φ ψ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (hψ : IsKfSmooth F ψ) :
    IsKfSmooth F (φ + ψ) :=
  IsSmoothVector.add hφ hψ

private theorem kfSmooth_smul_aux (F : Type) [Field F] [NumberField F]
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsKfSmooth F φ) (c : ℂ) : IsKfSmooth F (c • φ) := by
  unfold IsKfSmooth at hφ ⊢
  rw [isSmoothVector_iff_isOpen_stabilizer] at hφ ⊢
  refine Subgroup.isOpen_mono ?_ hφ
  intro g hg
  rw [MulAction.mem_stabilizer_iff] at hg ⊢
  refine RightTranslationFn.ext fun x => ?_
  have hx : φ (x * (g : AdelicGL2 (𝓞 F) F)) = φ x :=
    congrArg (fun f : RightTranslationFn (AdelicGL2 (𝓞 F) F) ℂ => RightTranslationFn.toFun f x) hg
  show c * φ (x * (g : AdelicGL2 (𝓞 F) F)) = c * φ x
  rw [hx]

private theorem integrable_constantTermIntegrand_of_continuous (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : Continuous φ) (g : AdelicGL2 (𝓞 F) F) :
    Integrable (constantTermIntegrand unipotentGL2 φ g)
      (productionPinsOf F D U gen (adelicBox F)).ν := by
  letI : MeasurableSpace (AdeleRing (𝓞 F) F) := AdelicHaar.adeleBorel (𝓞 F) F
  haveI : BorelSpace (AdeleRing (𝓞 F) F) := AdelicHaar.borelSpace_adeleBorel (𝓞 F) F
  haveI : (AdelicHaar.adelicAddHaar (𝓞 F) F).IsAddHaarMeasure :=
    AdelicHaar.isAddHaarMeasure_adelicAddHaar (𝓞 F) F
  have hc : Continuous fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g) :=
    hφ.comp ((continuous_unipotentGL2 (R := AdeleRing (𝓞 F) F)).mul continuous_const)
  obtain ⟨C, hC, hsub⟩ := exists_isCompact_adelicBox_subset F
  have hK : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) C
      (AdelicHaar.adelicAddHaar (𝓞 F) F) :=
    hc.continuousOn.integrableOn_compact hC
  have hbox : IntegrableOn (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g)) (adelicBox F)
      (AdelicHaar.adelicAddHaar (𝓞 F) F) :=
    hK.mono_set hsub
  have hne : (AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (adelicAddHaar_adelicBox_pos F).ne'
  show Integrable (fun q : AdeleRing (𝓞 F) F => φ (unipotentGL2 q * g))
    ((AdelicHaar.adelicAddHaar (𝓞 F) F (adelicBox F))⁻¹ •
      (AdelicHaar.adelicAddHaar (𝓞 F) F).restrict (adelicBox F))
  exact Integrable.smul_measure hbox hne

private theorem smoothCusp_add_aux (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    {ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ} {φ ψ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφc : Continuous φ) (hψc : Continuous ψ)
    (hφ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen (adelicBox F)) ξ φ)
    (hψ : IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen (adelicBox F)) ξ ψ) :
    IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen (adelicBox F)) ξ (φ + ψ) := by
  refine ⟨⟨automorphicFnAt_add_aux F hφ.1.1 hψ.1.1, ?_⟩, kfSmooth_add_aux F hφ.2 hψ.2⟩
  letI := (productionPinsOf F D U gen (adelicBox F)).nS
  exact IsCuspidalFn.add hφ.1.2 hψ.1.2
    (integrable_constantTermIntegrand_of_continuous F D U gen hφc)
    (integrable_constantTermIntegrand_of_continuous F D U gen hψc)

private theorem smoothCusp_smul_aux (F : Type) [Field F] [NumberField F] {pins : CarrierPins F}
    {ξ : pins.Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : IsSmoothCuspAutomorphicFnAt F pins ξ φ)
    (c : ℂ) : IsSmoothCuspAutomorphicFnAt F pins ξ (c • φ) := by
  refine ⟨⟨automorphicFnAt_smul_aux F hφ.1.1 c, ?_⟩, kfSmooth_smul_aux F hφ.2 c⟩
  letI := pins.nS
  exact IsCuspidalFn.smul hφ.1.2 c

private theorem continuous_and_smoothCusp_of_mem_cuspKFinite (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    {ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ) :
    Continuous φ ∧ IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen (adelicBox F)) ξ φ := by
  refine Submodule.span_induction
    (p := fun φ _ => Continuous φ ∧
      IsSmoothCuspAutomorphicFnAt F (productionPinsOf F D U gen (adelicBox F)) ξ φ) ?_ ?_ ?_ ?_ hφ
  · rintro φ ⟨hsat, hc, -⟩
    refine ⟨hc, ?_⟩
    have h1 := hsat 1
    rwa [rightTranslate_one_eq] at h1
  · exact ⟨continuous_zero, isSmoothCuspAutomorphicFnAt_zero F _ ξ⟩
  · intro u w _ _ hu hw
    exact ⟨hu.1.add hw.1, smoothCusp_add_aux F D U gen hu.1 hw.1 hu.2 hw.2⟩
  · intro c u _ hu
    exact ⟨hu.1.const_smul c, smoothCusp_smul_aux F hu.2 c⟩

end KFinite

section Subrep

variable (F : Type) [Field F] [NumberField F]

private theorem isCuspSubrep_inf_aux {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {A B : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hA : IsCuspSubrep F pins ξ A)
    (hB : IsCuspSubrep F pins ξ B) : IsCuspSubrep F pins ξ (A ⊓ B) where
  le := inf_le_left.trans hA.le
  rightTranslate_fin_mem g hg φ hφ :=
    Submodule.mem_inf.mpr ⟨hA.rightTranslate_fin_mem g hg φ (Submodule.mem_inf.mp hφ).1,
      hB.rightTranslate_fin_mem g hg φ (Submodule.mem_inf.mp hφ).2⟩
  rightTranslate_arch_mem w k φ hφ :=
    Submodule.mem_inf.mpr ⟨hA.rightTranslate_arch_mem w k φ (Submodule.mem_inf.mp hφ).1,
      hB.rightTranslate_arch_mem w k φ (Submodule.mem_inf.mp hφ).2⟩
  rightConv_mem f tys hf hbf φ hφ :=
    Submodule.mem_inf.mpr ⟨hA.rightConv_mem f tys hf hbf φ (Submodule.mem_inf.mp hφ).1,
      hB.rightConv_mem f tys hf hbf φ (Submodule.mem_inf.mp hφ).2⟩

private theorem isCuspSubrep_finsetSup_aux {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    (s : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ))) (hs : ∀ W ∈ s, IsCuspSubrep F pins ξ W) :
    IsCuspSubrep F pins ξ (s.sup id) where
  le := Finset.sup_le fun W hW => (hs W hW).le
  rightTranslate_fin_mem g hg :=
    map_mem_finsetSup_of_forall (T := rightTranslate F g) (M := cuspKFiniteSubmodule F pins ξ)
      (rightTranslate_zero F g) (fun φ ψ _ _ => rightTranslate_add F g φ ψ) s
      (fun W hW => (hs W hW).le) (fun W hW => (hs W hW).rightTranslate_fin_mem g hg)
  rightTranslate_arch_mem w k :=
    map_mem_finsetSup_of_forall (T := rightTranslate F (rowIsometryInclAt₀ F w k))
      (M := cuspKFiniteSubmodule F pins ξ) (rightTranslate_zero F _)
      (fun φ ψ _ _ => rightTranslate_add F _ φ ψ) s
      (fun W hW => (hs W hW).le) (fun W hW => (hs W hW).rightTranslate_arch_mem w k)
  rightConv_mem f tys hf hbf := by
    obtain ⟨hfc, hfs⟩ := continuous_and_hasCompactSupport_of_isFactorizableTestFn F f hf
    exact map_mem_finsetSup_of_forall (T := fun φ => rightConv F φ f)
      (M := cuspKFiniteSubmodule F pins ξ) (rightConv_zero_left F f)
      (fun φ ψ hφ hψ => rightConv_add_left F (continuous_of_mem_cuspKFinite F hφ)
        (continuous_of_mem_cuspKFinite F hψ) hfc hfs) s
      (fun W hW => (hs W hW).le) (fun W hW => (hs W hW).rightConv_mem f tys hf hbf)

private theorem le_finsetSup_of_mem_aux (s : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    {W : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hW : W ∈ s) : W ≤ s.sup id :=
  Finset.le_sup (f := id) hW

end Subrep

section TypePiece

variable {H G : Type*} [Group H] [Group G]
variable {W : Type*} [AddCommGroup W] [Module ℂ W]

private theorem exists_out_mul_eq (ι : H →* G) (x : G) :
    ∃ k : H, (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul ι.range x
  obtain ⟨k, hk⟩ := h.2
  exact ⟨k⁻¹, by rw [map_inv, hh, ← hk, mul_inv_cancel_right]⟩

private noncomputable def cosetCoord (ι : H →* G) (x : G) : H :=
  (exists_out_mul_eq ι x).choose

private theorem out_mul_cosetCoord (ι : H →* G) (x : G) :
    (QuotientGroup.mk x : G ⧸ ι.range).out * ι (cosetCoord ι x) = x :=
  (exists_out_mul_eq ι x).choose_spec

private theorem cosetCoord_unique {ι : H →* G} (hι : Function.Injective ι) {x : G} {k : H}
    (hk : (QuotientGroup.mk x : G ⧸ ι.range).out * ι k = x) : k = cosetCoord ι x :=
  hι (mul_left_cancel (hk.trans (out_mul_cosetCoord ι x).symm))

private theorem cosetCoord_mul {ι : H →* G} (hι : Function.Injective ι) (x : G) (k : H) :
    cosetCoord ι (x * ι k) = cosetCoord ι x * k := by
  symm
  apply cosetCoord_unique hι
  have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
    rw [QuotientGroup.eq]
    exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
  rw [hmk, map_mul, ← mul_assoc, out_mul_cosetCoord]

private theorem mem_typeSubmodule_of_isRightEquivariantOn {ι : H →* G} (hι : Function.Injective ι)
    (ρ : Representation ℂ H W) (P : Submodule ℂ W) (hP : ∀ (k : H), ∀ v ∈ P, ρ k v ∈ P)
    (S : P →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : P) (x : G), S ⟨ρ k v, hP k v v.2⟩ x = S v (x * ι k)) (v : P) :
    S v ∈ AutomorphicForm.typeSubmodule ι ρ := by
  classical

  let ℓ : G ⧸ ι.range → (P →ₗ[ℂ] ℂ) := fun c =>
    { toFun := fun p => S p c.out
      map_add' := fun p q => by rw [map_add]; rfl
      map_smul' := fun a p => by rw [map_smul]; rfl }
  have hext : ∀ c, ∃ g : W →ₗ[ℂ] ℂ, g.comp P.subtype = ℓ c := fun c => LinearMap.exists_extend (ℓ c)
  let ℓ' : G ⧸ ι.range → (W →ₗ[ℂ] ℂ) := fun c => (hext c).choose
  have hℓ' : ∀ c (p : P), ℓ' c (p : W) = S p c.out := fun c p => by
    have := LinearMap.congr_fun (hext c).choose_spec p
    simpa [ℓ] using this

  let T : W →ₗ[ℂ] (G → ℂ) :=
    { toFun := fun w x => ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) w)
      map_add' := fun w₁ w₂ => funext fun x => by simp only [map_add, Pi.add_apply]
      map_smul' := fun a w => funext fun x => by
        simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply] }
  have hT : AutomorphicForm.IsRightEquivariant ι ρ T := by
    intro k w x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (ρ k w)) =
      ℓ' (QuotientGroup.mk (x * ι k)) (ρ (cosetCoord ι (x * ι k)) w)
    have hmk : (QuotientGroup.mk (x * ι k) : G ⧸ ι.range) = QuotientGroup.mk x := by
      rw [QuotientGroup.eq]
      exact ⟨k⁻¹, by rw [map_inv, mul_inv_rev, inv_mul_cancel_right]⟩
    rw [hmk, cosetCoord_mul hι, map_mul]
    rfl
  have hTS : T (v : W) = S v := by
    funext x
    show ℓ' (QuotientGroup.mk x) (ρ (cosetCoord ι x) (v : W)) = S v x
    have hmem : ρ (cosetCoord ι x) (v : W) ∈ P := hP _ _ v.2
    have h1 := hℓ' (QuotientGroup.mk x) ⟨_, hmem⟩
    simp only at h1
    rw [h1, hS (cosetCoord ι x) v, out_mul_cosetCoord]
  rw [← hTS]
  exact AutomorphicForm.mem_typeSubmodule_of_isRightEquivariant hT _

end TypePiece

section PiRep

variable {H : Type*} [Group H]
variable {A : Type*} {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]

private def piRep (ρ : ∀ a, Representation ℂ H (W a)) : Representation ℂ H (∀ a, W a) where
  toFun k := LinearMap.pi fun a => (ρ a k).comp (LinearMap.proj a)
  map_one' := by
    ext v a
    simp
  map_mul' k₁ k₂ := by
    ext v a
    simp

private theorem piRep_apply (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (v : ∀ a, W a) (a : A) :
    piRep ρ k v a = ρ a k (v a) :=
  rfl

private theorem piRep_single [DecidableEq A] (ρ : ∀ a, Representation ℂ H (W a)) (k : H) (a : A)
    (v : W a) : piRep ρ k (Pi.single a v) = Pi.single a (ρ a k v) := by
  funext b
  rw [piRep_apply]
  by_cases hb : b = a
  · subst hb
    simp only [Pi.single_eq_same]
  · simp only [Pi.single_eq_of_ne hb, map_zero]

end PiRep

section Transport

variable {H G : Type*} [Group H] [Group G]

private theorem typeSubmodule_piRep_le {A : Type*} [Fintype A] [DecidableEq A] {W : A → Type*}
    [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] (ι : H →* G)
    (ρ : ∀ a, Representation ℂ H (W a)) :
    typeSubmodule ι (piRep ρ) ≤ ⨆ a, typeSubmodule ι (ρ a) := by
  refine Submodule.span_le.mpr ?_
  rintro f ⟨T, hT, v, rfl⟩
  show T v ∈ ⨆ a, typeSubmodule ι (ρ a)
  rw [← Finset.univ_sum_single v, map_sum]
  refine Submodule.sum_mem _ fun a _ => Submodule.mem_iSup_of_mem a ?_
  have hTa : IsRightEquivariant ι (ρ a) (T.comp (LinearMap.single ℂ W a)) := by
    intro k w x
    show T (Pi.single a (ρ a k w)) x = T (Pi.single a w) (x * ι k)
    rw [← piRep_single]
    exact hT k (Pi.single a w) x
  exact mem_typeSubmodule_of_isRightEquivariant hTa (v a)

private theorem mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi {A : Type*} [Fintype A] [DecidableEq A]
    {W : A → Type*} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)] {ι : H →* G}
    (hι : Function.Injective ι) (ρ : ∀ a, Representation ℂ H (W a)) (Q : Submodule ℂ (∀ a, W a))
    (hQ : ∀ (k : H), ∀ v ∈ Q, piRep ρ k v ∈ Q) (S : Q →ₗ[ℂ] (G → ℂ))
    (hS : ∀ (k : H) (v : Q) (x : G), S ⟨piRep ρ k v, hQ k v v.2⟩ x = S v (x * ι k)) (v : Q) :
    S v ∈ ⨆ a, typeSubmodule ι (ρ a) :=
  typeSubmodule_piRep_le ι ρ (mem_typeSubmodule_of_isRightEquivariantOn hι (piRep ρ) Q hQ S hS v)

private theorem exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G)
    (ρ : ∀ j, Representation ℂ H (W j)) {θ : G → ℂ} (hθ : θ ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    ∃ (t : Finset (G → ℂ)) (i : t → J) (Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ)),
      IsRightEquivariant ι (piRep fun a => ρ (i a)) Φ ∧ θ ∈ LinearMap.range Φ := by
  classical
  have h1 : θ ∈ Submodule.span ℂ
      (⋃ j, {f : G → ℂ | ∃ T : W j →ₗ[ℂ] (G → ℂ),
        IsRightEquivariant ι (ρ j) T ∧ f ∈ LinearMap.range T}) := by
    rw [Submodule.span_iUnion]
    exact hθ
  obtain ⟨t, ht, hθt⟩ := Submodule.mem_span_finite_of_mem_span h1
  have hgen : ∀ f : t, ∃ j : J, ∃ T : W j →ₗ[ℂ] (G → ℂ),
      IsRightEquivariant ι (ρ j) T ∧ (f : G → ℂ) ∈ LinearMap.range T := fun f => by
    have hf := ht f.2
    rw [Set.mem_iUnion] at hf
    obtain ⟨j, T, hT, hfT⟩ := hf
    exact ⟨j, T, hT, hfT⟩
  choose i T hT hfT using hgen
  let Φ : (∀ a : t, W (i a)) →ₗ[ℂ] (G → ℂ) := ∑ a : t, (T a).comp (LinearMap.proj a)
  have hΦ : ∀ w : ∀ a : t, W (i a), Φ w = ∑ a : t, T a (w a) := fun w => by
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
  refine ⟨t, i, Φ, ?_, ?_⟩
  · intro k w x
    rw [hΦ, hΦ, Finset.sum_apply, Finset.sum_apply]
    exact Finset.sum_congr rfl fun a _ => hT a k (w a) x
  · refine (Submodule.span_le.mpr ?_) hθt
    intro f hf
    obtain ⟨v, hv⟩ := hfT ⟨f, hf⟩
    refine ⟨Pi.single (⟨f, hf⟩ : t) v, ?_⟩
    rw [hΦ, Finset.sum_eq_single (⟨f, hf⟩ : t)]
    · rw [Pi.single_eq_same]
      exact hv
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, map_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h

private theorem mem_iSup_typeSubmodule_of_intertwines {G' : Type*} [Group G'] {J : Type*} {W : J → Type*}
    [∀ j, AddCommGroup (W j)] [∀ j, Module ℂ (W j)] (ι : H →* G) {ι' : H →* G'}
    (hι' : Function.Injective ι') (ρ : ∀ j, Representation ℂ H (W j)) (P₀ : Submodule ℂ (G → ℂ))
    (hP₀ : ∀ (k : H), ∀ θ ∈ P₀, (fun x => θ (x * ι k)) ∈ P₀) (A : P₀ →ₗ[ℂ] (G' → ℂ))
    (hA : ∀ (k : H) (θ : P₀) (y : G'), A ⟨fun x => (θ : G → ℂ) (x * ι k), hP₀ k θ θ.2⟩ y =
      A θ (y * ι' k))
    (θ : P₀) (hθ : (θ : G → ℂ) ∈ ⨆ j, typeSubmodule ι (ρ j)) :
    A θ ∈ ⨆ j, typeSubmodule ι' (ρ j) := by
  classical
  obtain ⟨t, i, Φ, hΦ, v, hv⟩ :=
    exists_isRightEquivariant_mem_range_of_mem_iSup_typeSubmodule ι ρ hθ
  have hQ : ∀ (k : H), ∀ w ∈ P₀.comap Φ, piRep (fun a => ρ (i a)) k w ∈ P₀.comap Φ := by
    intro k w hw
    rw [Submodule.mem_comap] at hw ⊢
    have hw' : Φ (piRep (fun a => ρ (i a)) k w) = fun x => Φ w (x * ι k) :=
      funext fun x => hΦ k w x
    rw [hw']
    exact hP₀ k _ hw
  let ΦQ : P₀.comap Φ →ₗ[ℂ] P₀ :=
    LinearMap.codRestrict P₀ (Φ.comp (P₀.comap Φ).subtype) fun w => w.2
  have hΦQ : ∀ w : P₀.comap Φ, ((ΦQ w : P₀) : G → ℂ) = Φ (w : ∀ a : t, W (i a)) := fun _ => rfl
  let S : P₀.comap Φ →ₗ[ℂ] (G' → ℂ) := A.comp ΦQ
  have hS : ∀ (k : H) (w : P₀.comap Φ) (y : G'),
      S ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ y = S w (y * ι' k) := by
    intro k w y
    have h1 : ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩ =
        ⟨fun x => ((ΦQ w : P₀) : G → ℂ) (x * ι k), hP₀ k _ (ΦQ w).2⟩ := by
      apply Subtype.ext
      funext x
      exact hΦ k w x
    show A (ΦQ ⟨piRep (fun a => ρ (i a)) k w, hQ k w w.2⟩) y = A (ΦQ w) (y * ι' k)
    rw [h1]
    exact hA k (ΦQ w) y
  have hv' : v ∈ P₀.comap Φ := by
    rw [Submodule.mem_comap, hv]
    exact θ.2
  have hmem := mem_iSup_typeSubmodule_of_isRightEquivariantOn_pi hι' (fun a => ρ (i a)) (P₀.comap Φ)
    hQ S hS ⟨v, hv'⟩
  have hSv : S ⟨v, hv'⟩ = A θ := by
    show A (ΦQ ⟨v, hv'⟩) = A θ
    congr 1
    exact Subtype.ext hv
  rw [hSv] at hmem
  exact (iSup_le fun a => le_iSup (fun j => typeSubmodule ι' (ρ j)) (i a)) hmem

end Transport

section RowIso

variable (F : Type) [Field F]

private theorem archComponent_archRowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (archRowIsometryInclAt₀ F w k) = (k : GL (Fin 2) w.Completion) :=
  archComponent_archGLIncl_self F w (k : GL (Fin 2) w.Completion)

variable [NumberField F]

private theorem archComponent_glArch_rowIsometryInclAt₀ (w : InfinitePlace F)
    (k : rowIsometrySubgroup₀ w.Completion) :
    archComponent F w (AdelicLevel.glArch (𝓞 F) F (rowIsometryInclAt₀ F w k))
      = (k : GL (Fin 2) w.Completion) := by
  rw [glArch_rowIsometryInclAt₀]
  exact archComponent_archRowIsometryInclAt₀ F w k

private theorem rowIsometryInclAt₀_injective (w : InfinitePlace F) :
    Function.Injective (rowIsometryInclAt₀ F w) := fun a b h => by
  have ha := archComponent_glArch_rowIsometryInclAt₀ F w a
  have hb := archComponent_glArch_rowIsometryInclAt₀ F w b
  rw [h] at ha
  exact Subtype.ext (ha.symm.trans hb)

end RowIso

section Projection

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem exists_isCompl_of_inf_eq_bot {A B : Submodule ℂ V} (hAB : A ⊓ B = ⊥) :
    ∃ B' : Submodule ℂ V, B ≤ B' ∧ IsCompl A B' := by
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (A ⊔ B)
  refine ⟨B ⊔ C, le_sup_left, ⟨?_, ?_⟩⟩
  · rw [Submodule.disjoint_def]
    intro x hxA hxBC
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hxBC
    have hzAB : z ∈ A ⊔ B := by
      have h1 : y + z - y ∈ A ⊔ B :=
        (A ⊔ B).sub_mem (Submodule.mem_sup_left hxA) (Submodule.mem_sup_right hy)
      rwa [add_sub_cancel_left] at h1
    have hz0 : z = 0 := Submodule.disjoint_def.mp hC.disjoint z hzAB hz
    subst hz0
    have hyAB : y + 0 ∈ A ⊓ B := Submodule.mem_inf.mpr ⟨hxA, by rw [add_zero]; exact hy⟩
    rw [hAB, Submodule.mem_bot] at hyAB
    exact hyAB
  · rw [codisjoint_iff, ← sup_assoc]
    exact codisjoint_iff.mp hC.codisjoint

private theorem exists_linearMap_add_eq_left {A B : Submodule ℂ V} (hAB : A ⊓ B = ⊥) :
    ∃ π : V →ₗ[ℂ] V, ∀ x ∈ A, ∀ y ∈ B, π (x + y) = x := by
  obtain ⟨B', hBB', hc⟩ := exists_isCompl_of_inf_eq_bot hAB
  refine ⟨A.subtype ∘ₗ Submodule.projectionOnto A B' hc, fun x hx y hy => ?_⟩
  have h1 : Submodule.projectionOnto A B' hc x = ⟨x, hx⟩ :=
    Submodule.projectionOnto_apply_left hc ⟨x, hx⟩
  have h2 : Submodule.projectionOnto A B' hc y = 0 :=
    Submodule.projectionOnto_apply_of_mem_right hc (hBB' hy)
  show A.subtype (Submodule.projectionOnto A B' hc (x + y)) = x
  rw [map_add, h1, h2, add_zero]
  rfl

end Projection

section ArchComponent

variable (F : Type) [Field F] [NumberField F]

private theorem component_mem_archCutSubmodule {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {A B : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hA : IsCuspSubrep F pins ξ A)
    (hB : IsCuspSubrep F pins ξ B) (hAB : A ⊓ B = ⊥) (tys : ArchTypeFamily F)
    {a b : AdelicGL2 (𝓞 F) F → ℂ} (ha : a ∈ A) (hb : b ∈ B)
    (hab : a + b ∈ archCutSubmodule F tys) : a ∈ archCutSubmodule F tys := by
  obtain ⟨π, hπ⟩ := exists_linearMap_add_eq_left hAB
  rw [mem_archCutSubmodule_iff] at hab ⊢
  intro w
  have hP₀ : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ θ ∈ A ⊔ B,
      (fun x => θ (x * rowIsometryInclAt₀ F w k)) ∈ A ⊔ B := by
    intro k θ hθ
    obtain ⟨θ₁, h₁, θ₂, h₂, rfl⟩ := Submodule.mem_sup.mp hθ
    show rightTranslate F (rowIsometryInclAt₀ F w k) (θ₁ + θ₂) ∈ A ⊔ B
    rw [rightTranslate_add]
    exact Submodule.add_mem_sup (hA.rightTranslate_arch_mem w k θ₁ h₁)
      (hB.rightTranslate_arch_mem w k θ₂ h₂)
  have hcomm : ∀ (k : rowIsometrySubgroup₀ w.Completion), ∀ θ ∈ A ⊔ B,
      π (rightTranslate F (rowIsometryInclAt₀ F w k) θ)
        = rightTranslate F (rowIsometryInclAt₀ F w k) (π θ) := by
    intro k θ hθ
    obtain ⟨θ₁, h₁, θ₂, h₂, rfl⟩ := Submodule.mem_sup.mp hθ
    rw [rightTranslate_add, hπ _ (hA.rightTranslate_arch_mem w k θ₁ h₁)
      _ (hB.rightTranslate_arch_mem w k θ₂ h₂), hπ θ₁ h₁ θ₂ h₂]
  have hmem : a + b ∈ A ⊔ B := Submodule.add_mem_sup ha hb
  have hab' : a + b ∈ ⨆ j : Fin (tys.card w),
      typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w j).ρ := hab w
  have key := mem_iSup_typeSubmodule_of_intertwines (rowIsometryInclAt₀ F w)
    (rowIsometryInclAt₀_injective F w) (fun j : Fin (tys.card w) => (tys.rep w j).ρ) (A ⊔ B) hP₀
    (π ∘ₗ (A ⊔ B).subtype) (fun k θ y => congrFun (hcomm k θ θ.2) y) ⟨a + b, hmem⟩ hab'
  have key' : π (a + b) ∈ ⨆ j : Fin (tys.card w),
      typeSubmodule (rowIsometryInclAt₀ F w) (tys.rep w j).ρ := key
  rw [hπ a ha b hb] at key'
  exact key'

end ArchComponent

section Generator

private theorem heckeGen_mem_finiteAdelicGL2Subgroup_aux (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) : heckeGen (𝓞 F) F v ∈ finiteAdelicGL2Subgroup F := by
  rw [mem_finiteAdelicGL2Subgroup_iff]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [glArch_apply, Units.val_one]
  exact heckeGenAt_fst _ i j

end Generator

section IsotypicSpan

variable (F : Type) [Field F] [NumberField F]

private theorem level_invariant_of_mem_isotypic {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ isotypicCuspSubmodule F pins ξ N S Ψ) :
    ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U N, φ (g * u) = φ g := by
  refine Submodule.span_induction
    (p := fun φ _ => ∀ g : AdelicGL2 (𝓞 F) F, ∀ u ∈ pins.U N, φ (g * u) = φ g) ?_ ?_ ?_ ?_ hφ
  · exact fun φ hφ => hφ.level_invariant
  · intro g u _
    rfl
  · intro x y _ _ hx hy g u hu
    simp only [Pi.add_apply, hx g u hu, hy g u hu]
  · intro c x _ hx g u hu
    simp only [Pi.smul_apply, hx g u hu]

private theorem central_eigen_of_mem_isotypic {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ isotypicCuspSubmodule F pins ξ N S Ψ) :
    ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (pins.gen v)) * g)
        = Ψ.toRawCentral.b v * φ g := by
  refine Submodule.span_induction
    (p := fun φ _ => ∀ v : HeightOneSpectrum (𝓞 F), v ∉ S → ∀ g : AdelicGL2 (𝓞 F) F,
      φ (centralScalar (𝓞 F) F (Matrix.GeneralLinearGroup.det (pins.gen v)) * g)
        = Ψ.toRawCentral.b v * φ g) ?_ ?_ ?_ ?_ hφ
  · exact fun φ hφ => hφ.central_eigen
  · intro v _ g
    simp only [Pi.zero_apply, mul_zero]
  · intro x y _ _ hx hy v hv g
    simp only [Pi.add_apply, hx v hv g, hy v hv g]
    ring
  · intro c x _ hx v hv g
    simp only [Pi.smul_apply, smul_eq_mul, hx v hv g]
    ring

private theorem heckeCosetSum_eq_of_mem_isotypic {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S)
    {reps : Fin (Ideal.absNorm v.asIdeal + 1) → AdelicGL2 (𝓞 F) F}
    (hsys : HeckeIntegralSeam.IsHeckeCosetSystem (pins.U N) (pins.gen v) reps) {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ isotypicCuspSubmodule F pins ξ N S Ψ) :
    ∀ g : AdelicGL2 (𝓞 F) F, SmoothCusp.heckeCosetSum F reps φ g = Ψ.a v * φ g := by
  refine Submodule.span_induction
    (p := fun φ _ => ∀ g : AdelicGL2 (𝓞 F) F, SmoothCusp.heckeCosetSum F reps φ g = Ψ.a v * φ g)
    ?_ ?_ ?_ ?_ hφ
  · intro φ₀ hφ₀ g
    obtain ⟨reps', hsys', heq⟩ := hφ₀.hecke_eigen v hv
    exact (HeckeIntegralSeam.heckeCosetSum_eq_of_isHeckeCosetSystem hsys hsys' hφ₀.level_invariant g).symm.trans
      (heq g)
  · intro g
    simp only [SmoothCusp.heckeCosetSum, Pi.zero_apply, Finset.sum_const_zero, mul_zero]
  · intro x y _ _ hx hy g
    have hx' := hx g
    have hy' := hy g
    simp only [SmoothCusp.heckeCosetSum] at hx' hy' ⊢
    simp only [Pi.add_apply, Finset.sum_add_distrib, hx', hy', mul_add]
  · intro c x _ hx g
    have hx' := hx g
    simp only [SmoothCusp.heckeCosetSum] at hx' ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, hx']
    ring

private theorem exists_isIsotypicCuspFormAt_of_ne_zero {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {N : Ideal (𝓞 F)} {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {v : AdelicGL2 (𝓞 F) F → ℂ} (hv : v ∈ isotypicCuspSubmodule F pins ξ N S Ψ) (hv0 : v ≠ 0) :
    ∃ φ₀ : AdelicGL2 (𝓞 F) F → ℂ, IsIsotypicCuspFormAt F pins ξ N S Ψ φ₀ := by
  by_contra h
  rw [not_exists] at h
  have hbot : isotypicCuspSubmodule F pins ξ N S Ψ = ⊥ :=
    (isotypicCuspSubmodule_eq_bot_iff F pins ξ N S Ψ).mpr fun φ hφ => absurd hφ (h φ)
  rw [hbot, Submodule.mem_bot] at hv
  exact hv0 hv

end IsotypicSpan

section CosetOp

variable (F : Type) [Field F] [NumberField F]

private def cosetOp {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F) (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    AdelicGL2 (𝓞 F) F → ℂ :=
  ∑ i, rightTranslate F (reps i) φ

private theorem cosetOp_apply {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F) :
    cosetOp F reps φ g = SmoothCusp.heckeCosetSum F reps φ g := by
  simp only [cosetOp, Finset.sum_apply, SmoothCusp.heckeCosetSum, rightTranslate_apply]

private theorem cosetOp_add {n : ℕ} (reps : Fin n → AdelicGL2 (𝓞 F) F)
    (φ ψ : AdelicGL2 (𝓞 F) F → ℂ) : cosetOp F reps (φ + ψ) = cosetOp F reps φ + cosetOp F reps ψ := by
  funext g
  simp only [cosetOp_apply, SmoothCusp.heckeCosetSum, Pi.add_apply, Finset.sum_add_distrib]

private theorem cosetOp_mem {pins : CarrierPins F} {ξ : pins.Z →* ℂˣ}
    {V : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)} (hV : IsCuspSubrep F pins ξ V) {n : ℕ}
    {reps : Fin n → AdelicGL2 (𝓞 F) F} (hreps : ∀ i, reps i ∈ finiteAdelicGL2Subgroup F)
    {φ : AdelicGL2 (𝓞 F) F → ℂ} (hφ : φ ∈ V) : cosetOp F reps φ ∈ V := by
  show (∑ i, rightTranslate F (reps i) φ) ∈ V
  exact V.sum_mem fun i _ => hV.rightTranslate_fin_mem (reps i) (hreps i) φ hφ

end CosetOp

section IsotypicComponent

variable (F : Type) [Field F] [NumberField F]

private theorem central_law_of_mem_cuspKFinite (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    {ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ} {φ : AdelicGL2 (𝓞 F) F → ℂ}
    (hφ : φ ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ)
    (d : (AdeleRing (𝓞 F) F)ˣ) (g : AdelicGL2 (𝓞 F) F) :
    φ (centralScalar (𝓞 F) F d * g) = ((ξ ⟨d, Subgroup.mem_top d⟩ : ℂˣ) : ℂ) * φ g := by
  have h := (continuous_and_smoothCusp_of_mem_cuspKFinite F D U gen hφ).2.1.1
  letI := (productionPinsOf F D U gen (adelicBox F)).mS
  exact ((lsXiMemberAt_iff (𝓞 F) F (productionPinsOf F D U gen (adelicBox F)).μ
    (productionPinsOf F D U gen (adelicBox F)).Z ξ (productionPinsOf F D U gen (adelicBox F)).D
    φ).mp h).1.central_transform ⟨d, Subgroup.mem_top d⟩ g

private theorem component_mem_isotypicCuspSubmodule (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (hU : ∀ N : Ideal (𝓞 F), U N ≤ finiteAdelicGL2Subgroup F)
    (hgen : ∀ v : HeightOneSpectrum (𝓞 F), gen v ∈ finiteAdelicGL2Subgroup F)
    {ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ} {N : Ideal (𝓞 F)}
    {S : Finset (HeightOneSpectrum (𝓞 F))} {Ψ : HeckeEigensystem F ℂ}
    {A B : Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)}
    (hA : IsCuspSubrep F (productionPinsOf F D U gen (adelicBox F)) ξ A)
    (hB : IsCuspSubrep F (productionPinsOf F D U gen (adelicBox F)) ξ B) (hAB : A ⊓ B = ⊥)
    {a b : AdelicGL2 (𝓞 F) F → ℂ} (ha : a ∈ A) (hb : b ∈ B)
    (hvI : a + b ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Ψ)
    (hv0 : a + b ≠ 0) :
    a ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Ψ := by
  obtain ⟨hac, hasc⟩ := continuous_and_smoothCusp_of_mem_cuspKFinite F D U gen (hA.le ha)
  obtain ⟨φ₀, hφ₀⟩ := exists_isIsotypicCuspFormAt_of_ne_zero F hvI hv0
  suffices h : IsIsotypicCuspFormAt F (productionPinsOf F D U gen (adelicBox F)) ξ N S Ψ a from
    h.mem_isotypicCuspSubmodule
  refine
    { smoothCusp := hasc
      continuous := hac
      level_invariant := ?_
      hecke_eigen := ?_
      central_eigen := ?_ }
  · intro g u hu
    have hu' : u ∈ finiteAdelicGL2Subgroup F := hU N hu
    have hL : rightTranslate F u (a + b) = (1 : ℂ) • (a + b) := by
      rw [one_smul]
      funext x
      exact level_invariant_of_mem_isotypic F hvI x u hu
    have key := map_eq_smul_of_inf_eq_bot hAB ha hb (hA.rightTranslate_fin_mem u hu' a ha)
      (hB.rightTranslate_fin_mem u hu' b hb) (rightTranslate_add F u a b) hL
    rw [one_smul] at key
    exact congrFun key g
  · intro v hv
    obtain ⟨reps, hsys, -⟩ := hφ₀.hecke_eigen v hv
    refine ⟨reps, hsys, ?_⟩
    have hreps : ∀ i, reps i ∈ finiteAdelicGL2Subgroup F := by
      intro i
      obtain ⟨u₁, hu₁, u₂, hu₂, hrep⟩ := HeckePair.mem_doubleCoset_iff.mp (hsys.mem_doubleCoset i)
      rw [← hrep]
      exact mul_mem (mul_mem (hU N hu₁) (hgen v)) (hU N hu₂)
    have hT : cosetOp F reps (a + b) = Ψ.a v • (a + b) := by
      funext g
      rw [cosetOp_apply, Pi.smul_apply, smul_eq_mul]
      exact heckeCosetSum_eq_of_mem_isotypic F hv hsys hvI g
    have key := map_eq_smul_of_inf_eq_bot hAB ha hb (cosetOp_mem F hA hreps ha)
      (cosetOp_mem F hB hreps hb) (cosetOp_add F reps a b) hT
    intro g
    have hg := congrFun key g
    rw [cosetOp_apply, Pi.smul_apply, smul_eq_mul] at hg
    exact hg
  · intro v hv g
    have hvK : a + b ∈ cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ :=
      (cuspKFiniteSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ).add_mem (hA.le ha)
        (hB.le hb)
    have hlaw := central_law_of_mem_cuspKFinite F D U gen hvK
      (Matrix.GeneralLinearGroup.det ((productionPinsOf F D U gen (adelicBox F)).gen v))
    have heig := central_eigen_of_mem_isotypic F hvI v hv
    obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hv0
    have hx₀' : (a + b) x₀ ≠ 0 := hx₀
    have hξ := mul_right_cancel₀ hx₀' ((hlaw x₀).symm.trans (heig x₀))
    have hlaw_a := central_law_of_mem_cuspKFinite F D U gen (hA.le ha)
      (Matrix.GeneralLinearGroup.det ((productionPinsOf F D U gen (adelicBox F)).gen v)) g
    exact hlaw_a.trans (congrArg (fun t : ℂ => t * a g) hξ)

end IsotypicComponent

section Assembly

variable (F : Type) [Field F] [NumberField F]

private theorem exists_mem_inf_inf_ne_bot_of_mem_sup (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)) (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ξ : (productionPinsOf F D U gen (adelicBox F)).Z →* ℂˣ)
    (hU : ∀ N : Ideal (𝓞 F), U N ≤ finiteAdelicGL2Subgroup F)
    (hgen : ∀ v : HeightOneSpectrum (𝓞 F), gen v ∈ finiteAdelicGL2Subgroup F) (N : Ideal (𝓞 F))
    (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ) (tys : ArchTypeFamily F)
    (v : AdelicGL2 (𝓞 F) F → ℂ)
    (hvI : v ∈ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Ψ)
    (hvT : v ∈ archCutSubmodule F tys) (hv0 : v ≠ 0)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ W ∈ 𝒱, IsCuspConstituent F (productionPinsOf F D U gen (adelicBox F)) ξ W)
    (hv : v ∈ 𝒱.sup id) :
    ∃ V ∈ 𝒱, V ⊓ isotypicCuspSubmodule F (productionPinsOf F D U gen (adelicBox F)) ξ N S Ψ ⊓
      archCutSubmodule F tys ≠ ⊥ := by
  classical
  induction 𝒱 using Finset.induction_on with
  | empty =>
    rw [Finset.sup_empty, Submodule.mem_bot] at hv
    exact absurd hv hv0
  | insert V₀ 𝒱' hV₀ ih =>
    have h𝒱' : ∀ W ∈ 𝒱', IsCuspConstituent F (productionPinsOf F D U gen (adelicBox F)) ξ W :=
      fun W hW => h𝒱 W (Finset.mem_insert_of_mem hW)
    have hV₀c := h𝒱 V₀ (Finset.mem_insert_self V₀ 𝒱')
    have hM : IsCuspSubrep F (productionPinsOf F D U gen (adelicBox F)) ξ (𝒱'.sup id) :=
      isCuspSubrep_finsetSup_aux F 𝒱' fun W hW => (h𝒱' W hW).1
    have hv' : v ∈ V₀ ⊔ 𝒱'.sup id := by
      rw [Finset.sup_insert] at hv
      exact hv
    rcases hV₀c.2.2 (V₀ ⊓ 𝒱'.sup id) (isCuspSubrep_inf_aux F hV₀c.1 hM) inf_le_left with hbot | heq
    · obtain ⟨a, ha, b, hb, hvab⟩ := Submodule.mem_sup.mp hv'
      subst hvab
      by_cases ha0 : a = 0
      · subst ha0
        have hb' : (0 : AdelicGL2 (𝓞 F) F → ℂ) + b ∈ 𝒱'.sup id := by
          rw [zero_add]
          exact hb
        obtain ⟨V, hV, hVne⟩ := ih h𝒱' hb'
        exact ⟨V, Finset.mem_insert_of_mem hV, hVne⟩
      · refine ⟨V₀, Finset.mem_insert_self V₀ 𝒱', ?_⟩
        rw [Submodule.ne_bot_iff]
        refine ⟨a, ?_, ha0⟩
        have haI := component_mem_isotypicCuspSubmodule F D U gen hU hgen hV₀c.1 hM hbot ha hb hvI hv0
        have haT := component_mem_archCutSubmodule F hV₀c.1 hM hbot tys ha hb hvT
        exact Submodule.mem_inf.mpr ⟨Submodule.mem_inf.mpr ⟨ha, haI⟩, haT⟩
    · have hle : V₀ ≤ 𝒱'.sup id := inf_eq_left.mp heq
      have hsup : V₀ ⊔ 𝒱'.sup id = 𝒱'.sup id := sup_eq_right.mpr hle
      rw [hsup] at hv'
      obtain ⟨V, hV, hVne⟩ := ih h𝒱' hv'
      exact ⟨V, Finset.mem_insert_of_mem hV, hVne⟩

end Assembly

end

theorem solution
    (F : Type) [Field F] [NumberField F] (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 F) F))
    (ξ : (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)).Z →* ℂˣ)
    (N : Ideal (𝓞 F)) (S : Finset (HeightOneSpectrum (𝓞 F))) (Ψ : HeckeEigensystem F ℂ)
    (tys : ArchTypeFamily F)
    (𝒱 : Finset (Submodule ℂ (AdelicGL2 (𝓞 F) F → ℂ)))
    (h𝒱 : ∀ W ∈ 𝒱, IsCuspConstituent F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ W)
    (v : AdelicGL2 (𝓞 F) F → ℂ) (hv : v ∈ 𝒱.sup id)
    (hvI : v ∈ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ)
    (hvT : v ∈ archCutSubmodule F tys) (hv0 : v ≠ 0) :
    ∃ V ∈ 𝒱,
      V ⊓ isotypicCuspSubmodule F (productionPinsOf F (⋃ x ∈ T, (· * x) '' centreCutSiegelSet F c u d₁ d₂)
        (fun N => levelOne (𝓞 F) F N ⊓ finiteAdelicGL2Subgroup F) (fun v => heckeGen (𝓞 F) F v)
        (adelicBox F)) ξ N S Ψ ⊓ archCutSubmodule F tys ≠ ⊥ := by
  exact exists_mem_inf_inf_ne_bot_of_mem_sup F _ _ _ ξ (fun _ => inf_le_right)
    (heckeGen_mem_finiteAdelicGL2Subgroup_aux F) N S Ψ tys v hvI hvT hv0 𝒱 h𝒱 hv

end S_LanglandsTunnell_exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup
end P2MW
export P2MW.S_LanglandsTunnell_exists_mem_finset_inf_isotypicCuspSubmodule_inf_archCutSubmodule_ne_bot_of_mem_sup (solution)
