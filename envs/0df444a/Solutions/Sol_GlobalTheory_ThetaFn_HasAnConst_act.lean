-- Prove2me | solution 1 for GlobalTheory.ThetaFn.HasAnConst.act
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:33:44.559215+00:00
-- url     : https://prove2.me/submissions/e3a3f384-18bd-4ba8-a33c-71085d0861ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_ExistsUniqueSecIsFnAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_AppellHumbertTrivialOfNowhereVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasAnConstThetaGrpZeroIff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_mem_twist_chart_iff
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translPt
import Theorems.Thm_GlobalTheory_ThetaFn_exAt_translT
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
private theorem exists_algChart_mem_source (hL : L.IsLB) (f : Sp ℂ ⟶ A.left) : ∃ i, ⊤ ≤ f ⁻¹ᵁ L.U i := by
  obtain ⟨cover, -, -⟩ := hL
  obtain ⟨a0⟩ : Nonempty (PrimeSpectrum ℂ) := inferInstance
  have hmem : f.base a0 ∈ (⨆ i, L.U i) := by
    rw [cover]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hmem
  refine ⟨i, fun a _ => ?_⟩
  have hsub : a = a0 := Subsingleton.elim (α := PrimeSpectrum ℂ) a a0
  rw [hsub]
  exact hi
private theorem valAt'_mul_of_top_le_preimage_open {X : Scheme.{0}} (y : Sp ℂ ⟶ X) (U : X.Opens) (a b : Γ(X, U)) :
    valAt' y U (a * b) = valAt' y U a * valAt' y U b := by
  unfold valAt'
  split_ifs with h
  · unfold valAt
    simp only [map_mul]
  · simp
private theorem valAt'_resG {X : Scheme.{0}} (y : Sp ℂ ⟶ X) {U V : X.Opens} (hVU : V ≤ U)
    (h : ⊤ ≤ y ⁻¹ᵁ V) (f : Γ(X, U)) :
    valAt' y V (X.presheaf.map (homOfLE hVU).op f) = valAt' y U f := by
  have h' : ⊤ ≤ y ⁻¹ᵁ U := fun a ha => hVU (h ha)
  unfold valAt'
  rw [dif_pos h, dif_pos h']
  unfold valAt
  exact congrArg (fun F => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom (F.hom f))
    (Scheme.Hom.map_appLE y h (homOfLE hVU).op)
private theorem valAt'_app_eq_valAt'_comp {X Y : Scheme.{0}} (y : Sp ℂ ⟶ X) (φ : X ⟶ Y) (U : Y.Opens)
    (f : Γ(Y, U)) : valAt' y (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (y ≫ φ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ (y ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h, dif_pos h']
    unfold valAt
    rw [Scheme.Hom.comp_appLE]
    rfl
  · have h' : ¬ ⊤ ≤ y ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_neg h, dif_neg h']
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
private theorem exAt_preimage_wchart_eq_univ (z : Fin g → ℂ) (i : L.ι)
    (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ L.U i) :
    ⊤ ≤ exAt u p z ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => (snd T A).left) (fun _ => i) := by
  have h0 : exAt u p z ≫ (snd T A).left = (u.ex z).left := by
    unfold exAt
    rw [← Over.comp_left, lift_snd]
  rw [← h0] at h
  intro a ha
  refine Set.mem_iInter.2 (fun _ => ?_)
  simpa using h ha
end GlobalTheory.ThetaFn
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory GlobalTheory.ThetaFn
open CubeValues SymmetricSemicharacter AppellHumbertTrivial
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
  {T : Over (Sp ℂ)} (p : 𝟙_ (Over (Sp ℂ)) ⟶ T)
variable {u p} {Hm : Matrix (Fin g) (Fin g) ℂ} {k : ℤ} {Θ : ThetaGrp A L k T} {x : Fin g → ℂ}
namespace GlobalTheory.ThetaFn
namespace HasAnConst
theorem _root_.solution (hL : L.IsLB) {c : ℂ} (h : HasAnConst u p Hm Θ x c)
    {s s' : LB.Sec (LPow A L k T)} (hs : IsActOf A L k Θ s s') {θ θ' : (Fin g → ℂ) → ℂ}
    (hθ : IsFnAt u p k s θ) (hθ' : IsFnAt u p k s' θ') (z : Fin g → ℂ) :
    θ' z = c * fockFactor Hm k x z * θ (z + x) := by
  obtain ⟨i0, hi0⟩ := exists_algChart_mem_source hL (u.ex z).left
  obtain ⟨i1, hi1⟩ := exists_algChart_mem_source hL (u.ex (z + x)).left
  have hch := (exAt_mem_twist_chart_iff u p (exAt_translPt u h.1 z) ![i0, i1]).2 ⟨hi0, hi1⟩
  have e : valAt' (exAt u p z) (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1])
      (Θ.φ.s ![i0, i1]).val * u.fr i1 (z + x) ^ k = c * fockFactor Hm k x z * u.fr i0 z ^ k :=
    h.2 ![i0, i1] z hi0 hi1
  unfold IsActOf IsTwistPull at hs
  have hs1 := congrArg (valAt' (exAt u p z) _) (hs ![i0, i1])
  erw [valAt'_mul_of_top_le_preimage_open, valAt'_resG _ _ hch, valAt'_resG _ _ hch, valAt'_app_eq_valAt'_comp,
    exAt_translT u h.1 z] at hs1
  have A1 : valAt' (exAt u p z) ((LPow A L k T).U fun _ => i0) (s'.f fun _ => i0) = θ' z * u.fr i0 z ^ k :=
    hθ' (fun _ => i0) z (exAt_preimage_wchart_eq_univ z i0 hi0)
  have A2 : valAt' (exAt u p (z + x)) ((LPow A L k T).U fun _ => i1) (s.f fun _ => i1) =
      θ (z + x) * u.fr i1 (z + x) ^ k :=
    hθ (fun _ => i1) (z + x) (exAt_preimage_wchart_eq_univ (z + x) i1 hi1)
  have key : θ' z * u.fr i0 z ^ k = valAt' (exAt u p z)
      (LB.wchart L ![(snd T A).left, (translPt A Θ.pt).left] ![i0, i1]) (Θ.φ.s ![i0, i1]).val *
      (θ (z + x) * u.fr i1 (z + x) ^ k) := by
    rw [← A1, ← A2]
    exact hs1
  have hfr0 : u.fr i0 z ^ k ≠ 0 := zpow_ne_zero _ (u.fr_ne _ _ hi0)
  apply mul_right_cancel₀ hfr0
  linear_combination key + θ (z + x) * e
end HasAnConst
end GlobalTheory.ThetaFn
