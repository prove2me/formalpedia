-- Prove2me | solution 1 for IharaTower.exists_levelPairing_cornerSubmodule_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/3de540db-80f6-57d6-9951-ea4e222c5753

import Definitions.Def_HeckeModule_IharaRungDatum
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_le

set_option autoImplicit false

namespace CpairK7sol

open IharaLemma IharaTower

variable {𝒪 : Type} [CommRing 𝒪]
variable {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
variable {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]

noncomputable def projW (W : Submodule 𝕋 V) (e : 𝕋) :
    W →ₗ[𝒪] ↥(cornerSubmodule (M := V) e) where
  toFun w := ⟨e • (w : V), ⟨(w : V), rfl⟩⟩
  map_add' x y := Subtype.ext (by simp [smul_add])
  map_smul' r x := Subtype.ext (by
    show e • ((r • x : W) : V) = r • (e • (x : V))
    rw [Submodule.coe_smul_of_tower, smul_comm])

@[scoped simp] theorem projW_coe (W : Submodule 𝕋 V) (e : 𝕋) (w : W) :
    ((projW (𝒪 := 𝒪) W e w : cornerSubmodule (M := V) e) : V) = e • (w : V) := rfl

noncomputable def inclW (W : Submodule 𝕋 V) (e : 𝕋)
    (h : cornerSubmodule (M := V) e ≤ W) : ↥(cornerSubmodule (M := V) e) →ₗ[𝒪] W where
  toFun x := ⟨(x : V), h x.2⟩
  map_add' _ _ := Subtype.ext rfl
  map_smul' _ _ := Subtype.ext rfl

@[scoped simp] theorem inclW_coe (W : Submodule 𝕋 V) (e : 𝕋)
    (h : cornerSubmodule (M := V) e ≤ W) (x : cornerSubmodule (M := V) e) :
    ((inclW (𝒪 := 𝒪) W e h x : W) : V) = x := rfl

theorem inclW_eq_inclusion (W : Submodule 𝕋 V) (e : 𝕋)
    (h : cornerSubmodule (M := V) e ≤ W) (x : cornerSubmodule (M := V) e) :
    inclW (𝒪 := 𝒪) W e h x = Submodule.inclusion h x := rfl

end CpairK7sol
p2m_reactivate "P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_le.CpairK7sol"

open CpairK7sol in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {𝕋 : Type} [CommRing 𝕋] [Algebra 𝒪 𝕋]
    {V : Type} [AddCommGroup V] [Module 𝒪 V] [Module 𝕋 V] [IsScalarTower 𝒪 𝕋 V]
    (W : Submodule 𝕋 V) (B : W →ₗ[𝒪] W →ₗ[𝒪] 𝒪) (hB : Function.Bijective B)
    (hadj : ∀ (t : 𝕋) (x y : W), B (t • x) y = B x (t • y))
    (S : IharaLemma.IdempotentSplitting 𝕋) (i : Fin S.n)
    (hle : IharaLemma.cornerSubmodule (M := V) (S.e i) ≤ W) :
    ∃ P : IharaTower.LevelPairing (𝒪 := 𝒪) (S.CornerRing i)
        ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
      ∀ x y : ↥(IharaLemma.cornerSubmodule (M := V) (S.e i)),
        P.B x y = B (Submodule.inclusion hle x) (Submodule.inclusion hle y) := by
  open IharaLemma IharaTower in
  classical
  have hidem : S.e i * S.e i = S.e i := (S.idem i).eq

  let ι : ↥(cornerSubmodule (M := V) (S.e i)) →ₗ[𝒪] W := inclW (𝒪 := 𝒪) W (S.e i) hle
  let Bc : ↥(cornerSubmodule (M := V) (S.e i)) →ₗ[𝒪]
      ↥(cornerSubmodule (M := V) (S.e i)) →ₗ[𝒪] 𝒪 :=
    (B.comp ι).compl₂ ι
  have hBc : ∀ x y, Bc x y = B (ι x) (ι y) := fun x y => rfl

  have hfix : ∀ x : ↥(cornerSubmodule (M := V) (S.e i)), S.e i • (x : V) = x := fun x =>
    S.e_smul_coe i x
  have hιfix : ∀ x : ↥(cornerSubmodule (M := V) (S.e i)), S.e i • ι x = ι x := by
    intro x; apply Subtype.ext; simp [ι, hfix x]

  have hιproj : ∀ w : W, ι (projW (𝒪 := 𝒪) W (S.e i) w) = S.e i • w := by
    intro w; apply Subtype.ext; simp [ι]
  refine ⟨⟨Bc, ?_, ?_⟩, fun x y => rfl⟩
  ·
    intro z m n
    rw [hBc, hBc]
    have h1 : ι (z • m) = (z : 𝕋) • ι m := Subtype.ext rfl
    have h2 : ι (z • n) = (z : 𝕋) • ι n := Subtype.ext rfl
    rw [h1, h2, hadj]
  ·
    constructor
    ·
      intro x x' hxx'
      have hW : B (ι x) = B (ι x') := by
        ext w
        have key : ∀ y : ↥(cornerSubmodule (M := V) (S.e i)),
            B (ι y) w = Bc y (projW (𝒪 := 𝒪) W (S.e i) w) := by
          intro y
          rw [hBc, hιproj, ← hadj, hιfix]
        rw [key, key, hxx']
      have := hB.1 hW
      exact Subtype.ext (congrArg (fun w : W => (w : V)) this)
    ·
      intro μ

      obtain ⟨w, hw⟩ := hB.2 (μ.comp (projW (𝒪 := 𝒪) W (S.e i)))
      refine ⟨projW (𝒪 := 𝒪) W (S.e i) w, ?_⟩
      ext y
      rw [hBc, hιproj, hadj, hιfix, hw]
      simp only [LinearMap.coe_comp, Function.comp_apply]
      congr 1
      apply Subtype.ext
      show S.e i • ((ι y : W) : V) = (y : V)
      exact hfix y

end S_IharaTower_exists_levelPairing_cornerSubmodule_of_le
end P2MW
export P2MW.S_IharaTower_exists_levelPairing_cornerSubmodule_of_le (solution)
