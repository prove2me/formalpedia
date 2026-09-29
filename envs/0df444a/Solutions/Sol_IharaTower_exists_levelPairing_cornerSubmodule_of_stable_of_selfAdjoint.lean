-- Prove2me | solution 1 for IharaTower.exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/feef6795-8263-5cbe-baa4-3a74a3839c3a

import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_CohCarrier_Inst
import Definitions.Def_ModularCurve_PeriodMap
import Definitions.Def_HeckeModule_IharaRungDatum
import Theorems.Thm_IharaTower_exists_levelPairing_cornerSubmodule_of_le
import Theorems.Thm_CohCarrier_heckeT_mem_parabolicHoms
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_coprime
import Theorems.Thm_CohCarrier_iDeg_heckeT_comm_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint

set_option autoImplicit false

open CohCarrier IharaLemma IharaTower

namespace CohL2
namespace ObligP

section Core

variable {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
  {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]

theorem exists_levelPairing_of_stable
    (W₀ : Submodule 𝒪 V) (hstab : ∀ (t : 𝕋) (w : V), w ∈ W₀ → t • w ∈ W₀)
    (B : W₀ →ₗ[𝒪] W₀ →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y Tx Ty : W₀), (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) →
      B Tx y = B x Ty)
    (S : IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) → v ∈ W₀) :
    ∃ P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i) ↥(cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(cornerSubmodule (M := V) (S.e i)),
        P.B x y = B ⟨(x : V), hle _ x.2⟩ ⟨(y : V), hle _ y.2⟩ := by
  let W : Submodule 𝕋 V :=
    { carrier := W₀
      add_mem' := fun ha hb => W₀.add_mem ha hb
      zero_mem' := W₀.zero_mem
      smul_mem' := fun t w hw => hstab t w hw }
  let e : ↥W ≃ₗ[𝒪] ↥W₀ :=
    { toFun := fun w => ⟨(w : V), w.2⟩
      invFun := fun w => ⟨(w : V), w.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let B' : ↥W →ₗ[𝒪] ↥W →ₗ[𝒪] 𝒪 := B.compl₁₂ e.toLinearMap e.toLinearMap
  have hB'app : ∀ x y : ↥W, B' x y = B (e x) (e y) := fun x y => rfl
  have hB' : Function.Bijective B' := by
    constructor
    · intro x x' h
      have h2 : B (e x) = B (e x') := by
        apply LinearMap.ext; intro w₀
        have := LinearMap.congr_fun h (e.symm w₀)
        rw [hB'app, hB'app, LinearEquiv.apply_symm_apply] at this
        exact this
      exact e.injective (hB.1 h2)
    · intro g
      obtain ⟨x₀, hx₀⟩ := hB.2 (g.comp e.symm.toLinearMap)
      refine ⟨e.symm x₀, ?_⟩
      apply LinearMap.ext; intro w
      rw [hB'app, LinearEquiv.apply_symm_apply, hx₀, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.symm_apply_apply]
  have hadj' : ∀ (t : 𝕋) (x y : ↥W), B' (t • x) y = B' x (t • y) := by
    intro t x y
    rw [hB'app, hB'app]
    exact hadj t (e x) (e y) (e (t • x)) (e (t • y)) rfl rfl
  have hle' : cornerSubmodule (M := V) (S.e i) ≤ W := fun v hv => hle v hv
  obtain ⟨P, hP⟩ := IharaTower.exists_levelPairing_cornerSubmodule_of_le W B' hB' hadj' S i hle'
  exact ⟨P, fun x y => hP x y⟩

theorem stable_adj_of_adjoin_eq_top
    (W₀ : Submodule 𝒪 V) (B : W₀ →ₗ[𝒪] W₀ →ₗ[𝒪] 𝒪) (G : Set 𝕋) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hgen : ∀ g ∈ G, (∀ w : V, w ∈ W₀ → g • w ∈ W₀) ∧
      (∀ x y Tx Ty : W₀, (Tx : V) = g • (x : V) → (Ty : V) = g • (y : V) → B Tx y = B x Ty)) :
    ∀ t : 𝕋, (∀ w : V, w ∈ W₀ → t • w ∈ W₀) ∧
      (∀ x y Tx Ty : W₀, (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) → B Tx y = B x Ty) := by
  intro t
  have ht : t ∈ Algebra.adjoin 𝒪 G := hG ▸ Algebra.mem_top
  refine Algebra.adjoin_induction (p := fun s _ => (∀ w : V, w ∈ W₀ → s • w ∈ W₀) ∧
      (∀ x y Tx Ty : W₀, (Tx : V) = s • (x : V) → (Ty : V) = s • (y : V) → B Tx y = B x Ty))
    ?_ ?_ ?_ ?_ ht
  · exact fun g hg => hgen g hg
  · intro r
    refine ⟨fun w hw => ?_, fun x y Tx Ty hTx hTy => ?_⟩
    · rw [algebraMap_smul]; exact W₀.smul_mem r hw
    · rw [algebraMap_smul] at hTx hTy
      have ex : Tx = r • x := Subtype.ext hTx
      have ey : Ty = r • y := Subtype.ext hTy
      rw [ex, ey, map_smul, LinearMap.smul_apply, map_smul, smul_eq_mul]
  · intro a b _ _ ha hb
    refine ⟨fun w hw => ?_, fun x y Tx Ty hTx hTy => ?_⟩
    · rw [add_smul]; exact W₀.add_mem (ha.1 w hw) (hb.1 w hw)
    · rw [add_smul] at hTx hTy
      have ex : Tx = ⟨a • (x : V), ha.1 _ x.2⟩ + ⟨b • (x : V), hb.1 _ x.2⟩ := Subtype.ext hTx
      have ey : Ty = ⟨a • (y : V), ha.1 _ y.2⟩ + ⟨b • (y : V), hb.1 _ y.2⟩ := Subtype.ext hTy
      rw [ex, ey, map_add, LinearMap.add_apply, map_add,
        ha.2 x y ⟨a • (x : V), ha.1 _ x.2⟩ ⟨a • (y : V), ha.1 _ y.2⟩ rfl rfl,
        hb.2 x y ⟨b • (x : V), hb.1 _ x.2⟩ ⟨b • (y : V), hb.1 _ y.2⟩ rfl rfl]
  · intro a b _ _ ha hb
    refine ⟨fun w hw => ?_, fun x y Tx Ty hTx hTy => ?_⟩
    · rw [mul_smul]; exact ha.1 _ (hb.1 w hw)
    ·
      have hTx' : (Tx : V) = a • ((⟨b • (x : V), hb.1 _ x.2⟩ : W₀) : V) := by rw [hTx, mul_smul]
      have hTy' : (Ty : V) = b • ((⟨a • (y : V), ha.1 _ y.2⟩ : W₀) : V) := by
        rw [hTy, mul_comm, mul_smul]
      rw [ha.2 ⟨b • (x : V), hb.1 _ x.2⟩ y Tx ⟨a • (y : V), ha.1 _ y.2⟩ hTx' rfl,
        hb.2 x ⟨a • (y : V), ha.1 _ y.2⟩ ⟨b • (x : V), hb.1 _ x.2⟩ Ty rfl hTy']

end Core

section Generators

variable {𝒪 : Type} [CommRing 𝒪] (M : ℕ) [NeZero M] (Hs : Subgroup (ZMod M)ˣ) (h₁ : LevelLE M M ⊤ Hs 1)

abbrev Wsub : Submodule 𝒪 (H1 M Hs 𝒪) :=
  (ModularCurve.Period.parabolicHoms 𝒪 (GammaH M ⊤) 𝒪).map (iDegL M M ⊤ Hs 1 𝒪 𝒪 h₁)

theorem heckeT_mem_Wsub (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime ∨ ℓ ∣ M)
    (w : H1 M Hs 𝒪) (hw : w ∈ Wsub M Hs h₁) : heckeT M Hs ℓ 𝒪 w ∈ Wsub (𝒪 := 𝒪) M Hs h₁ := by
  rw [Submodule.mem_map] at hw ⊢
  obtain ⟨x₀, hx₀, rfl⟩ := hw
  refine ⟨heckeT M ⊤ ℓ 𝒪 x₀, ?_, ?_⟩
  · rw [ModularCurve.Period.mem_parabolicHoms_iff] at hx₀ ⊢
    exact (ModularCurve.Period.mem_parabolicHoms_iff (R := ℤ)).mp
      (CohCarrier.heckeT_mem_parabolicHoms M ⊤ 𝒪 ℓ x₀
        ((ModularCurve.Period.mem_parabolicHoms_iff (R := ℤ)).mpr hx₀))
  · show iDeg' M M ⊤ Hs 1 𝒪 h₁ (heckeT M ⊤ ℓ 𝒪 x₀) = heckeT M Hs ℓ 𝒪 (iDeg' M M ⊤ Hs 1 𝒪 h₁ x₀)
    by_cases hℓM : ℓ ∣ M
    · exact CohCarrier.iDeg_heckeT_comm_of_dvd h₁ (Nat.coprime_one_right ℓ) hℓM x₀
    · exact CohCarrier.iDeg_heckeT_comm_of_coprime h₁ (Nat.coprime_one_right ℓ) (hℓ.resolve_right hℓM) hℓM x₀

variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋] [Module 𝕋 (H1 M Hs 𝒪)] [IsScalarTower 𝒪 𝕋 (H1 M Hs 𝒪)]

theorem gen_stable_adj
    (B : ↥(Wsub (𝒪 := 𝒪) M Hs h₁) →ₗ[𝒪] ↥(Wsub (𝒪 := 𝒪) M Hs h₁) →ₗ[𝒪] 𝒪)
    (hT : ∀ (ℓ : ℕ) [NeZero ℓ], (ℓ.Prime ∨ ℓ ∣ M) →
      ∀ (x y Tx Ty : ↥(Wsub (𝒪 := 𝒪) M Hs h₁)),
        (Tx : H1 M Hs 𝒪) = heckeT M Hs ℓ 𝒪 x → (Ty : H1 M Hs 𝒪) = heckeT M Hs ℓ 𝒪 y →
        B Tx y = B x Ty)
    (hD : ∀ (d : (ZMod M)ˣ) (x : ↥(Wsub (𝒪 := 𝒪) M Hs h₁)), diamondL M Hs 𝒪 d (x : H1 M Hs 𝒪) = x)
    (g : 𝕋)
    (hg : (∃ (ℓ : ℕ) (_ : NeZero ℓ), (ℓ.Prime ∨ ℓ ∣ M) ∧ ∀ v : H1 M Hs 𝒪, g • v = heckeT M Hs ℓ 𝒪 v) ∨
      (∃ d : (ZMod M)ˣ, ∀ v : H1 M Hs 𝒪, g • v = diamondL M Hs 𝒪 d v)) :
    (∀ w : H1 M Hs 𝒪, w ∈ Wsub (𝒪 := 𝒪) M Hs h₁ → g • w ∈ Wsub (𝒪 := 𝒪) M Hs h₁) ∧
      (∀ x y Tx Ty : ↥(Wsub (𝒪 := 𝒪) M Hs h₁), (Tx : H1 M Hs 𝒪) = g • (x : H1 M Hs 𝒪) →
        (Ty : H1 M Hs 𝒪) = g • (y : H1 M Hs 𝒪) → B Tx y = B x Ty) := by
  rcases hg with ⟨ℓ, _, hℓ, hg⟩ | ⟨d, hg⟩
  · refine ⟨fun w hw => ?_, fun x y Tx Ty hTx hTy => ?_⟩
    · rw [hg]; exact heckeT_mem_Wsub M Hs h₁ ℓ hℓ w hw
    · rw [hg] at hTx hTy
      exact hT ℓ hℓ x y Tx Ty hTx hTy
  · refine ⟨fun w hw => ?_, fun x y Tx Ty hTx hTy => ?_⟩
    · rw [hg, hD d ⟨w, hw⟩]; exact hw
    · rw [hg, hD d x] at hTx
      rw [hg, hD d y] at hTy
      rw [Subtype.ext hTx, Subtype.ext hTy]

theorem oblig_p
    (Sp : IdempotentSplitting 𝕋) (i : Fin Sp.n)
    (B : ↥(Wsub (𝒪 := 𝒪) M Hs h₁) →ₗ[𝒪] ↥(Wsub (𝒪 := 𝒪) M Hs h₁) →ₗ[𝒪] 𝒪)
    (hB : Function.Bijective B)
    (hT : ∀ (ℓ : ℕ) [NeZero ℓ], (ℓ.Prime ∨ ℓ ∣ M) →
      ∀ (x y Tx Ty : ↥(Wsub (𝒪 := 𝒪) M Hs h₁)),
        (Tx : H1 M Hs 𝒪) = heckeT M Hs ℓ 𝒪 x → (Ty : H1 M Hs 𝒪) = heckeT M Hs ℓ 𝒪 y →
        B Tx y = B x Ty)
    (hD : ∀ (d : (ZMod M)ˣ) (x : ↥(Wsub (𝒪 := 𝒪) M Hs h₁)), diamondL M Hs 𝒪 d (x : H1 M Hs 𝒪) = x)
    (G : Set 𝕋) (hG : Algebra.adjoin 𝒪 G = ⊤)
    (hGop : ∀ g ∈ G,
      (∃ (ℓ : ℕ) (_ : NeZero ℓ), (ℓ.Prime ∨ ℓ ∣ M) ∧ ∀ v : H1 M Hs 𝒪, g • v = heckeT M Hs ℓ 𝒪 v) ∨
      (∃ d : (ZMod M)ˣ, ∀ v : H1 M Hs 𝒪, g • v = diamondL M Hs 𝒪 d v))
    (hle : ∀ v : H1 M Hs 𝒪, v ∈ cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i) → v ∈ Wsub (𝒪 := 𝒪) M Hs h₁) :
    ∃ P : LevelPairing (𝒪 := 𝒪) (Sp.CornerRing i) ↥(cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i)),
      ∀ x y : ↥(cornerSubmodule (M := H1 M Hs 𝒪) (Sp.e i)),
        P.B x y = B ⟨(x : H1 M Hs 𝒪), hle _ x.2⟩ ⟨(y : H1 M Hs 𝒪), hle _ y.2⟩ := by
  have hall := stable_adj_of_adjoin_eq_top (Wsub (𝒪 := 𝒪) M Hs h₁) B G hG
    (fun g hg => gen_stable_adj M Hs h₁ B hT hD g (hGop g hg))
  exact exists_levelPairing_of_stable (Wsub (𝒪 := 𝒪) M Hs h₁) (fun t => (hall t).1) B hB
    (fun t => (hall t).2) Sp i hle

end Generators

end CohL2.ObligP

open IharaLemma IharaTower in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (W₀ : Submodule 𝒪 V) (hstab : ∀ (t : 𝕋) (w : V), w ∈ W₀ → t • w ∈ W₀)
    (B : W₀ →ₗ[𝒪] W₀ →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y Tx Ty : W₀), (Tx : V) = t • (x : V) → (Ty : V) = t • (y : V) →
      B Tx y = B x Ty)
    (S : IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : ∀ v : V, v ∈ cornerSubmodule (M := V) (S.e i) → v ∈ W₀) :
    ∃ P : LevelPairing (𝒪 := 𝒪) (S.CornerRing i) ↥(cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(cornerSubmodule (M := V) (S.e i)),
        P.B x y = B ⟨(x : V), hle _ x.2⟩ ⟨(y : V), hle _ y.2⟩ :=
  CohL2.ObligP.exists_levelPairing_of_stable W₀ hstab B hB hadj S i hle

end S_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint
end P2MW
export P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_stable_of_selfAdjoint (solution)
