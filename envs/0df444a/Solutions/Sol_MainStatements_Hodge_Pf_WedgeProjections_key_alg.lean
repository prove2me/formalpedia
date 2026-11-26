-- Prove2me | solution 1 for MainStatements.Hodge.Pf.WedgeProjections.key_alg
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:44:21.784474+00:00
-- url     : https://prove2.me/submissions/3bedb77c-f4f2-4b7c-8dd5-838981e9e35e

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_AbelianDeRham_AbelianWedgeProducts_ThetaMulti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MainStatements MainStatements.Hodge MainStatements.Hodge.Pf MainStatements.Hodge.Pf.WedgeProjections
theorem _root_.solution {K : Type} [Field K] {V W : Type} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (p q : V →ₗ[K] W) (r₁ r₂ : W →ₗ[K] V) (h11 : r₁ ∘ₗ p = LinearMap.id) (h12 : r₁ ∘ₗ q = 0)
    (h21 : r₂ ∘ₗ p = 0) (h22 : r₂ ∘ₗ q = LinearMap.id) (t : ⋀[K]^2 V)
    (ht : exteriorPower.map 2 (p + q) t = exteriorPower.map 2 p t + exteriorPower.map 2 q t) : t = 0 := by
  classical
  set bK := Module.Basis.ofVectorSpace K V with hbK
  set ι := Module.Basis.ofVectorSpaceIndex K V
  letI : LinearOrder ι := IsWellOrder.linearOrder (WellOrderingRel : ι → ι → Prop)
  -- the upper-triangular half of the wedge: a left inverse of antisymmetrisation, valid in every characteristic
  let g : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V :=
    bK.constr K fun i => bK.constr K fun j => if i < j then exteriorPower.ιMulti K 2 ![bK i, bK j] else 0
  have hg : ∀ i j, g (bK i) (bK j) = if i < j then exteriorPower.ιMulti K 2 ![bK i, bK j] else 0 := by
    intro i j; simp only [g, Module.Basis.constr_basis]
  have hswap : ∀ a b : V, exteriorPower.ιMulti K 2 ![b, a] = - exteriorPower.ιMulti K 2 ![a, b] := by
    intro a b
    have h := (exteriorPower.ιMulti K 2 (M := V)).map_swap ![a, b] (i := 0) (j := 1) (by decide)
    have e : (![a, b] : Fin 2 → V) ∘ Equiv.swap 0 1 = ![b, a] := by
      funext k; fin_cases k <;> simp
    rw [e] at h; exact h
  have hself : ∀ a : V, exteriorPower.ιMulti K 2 ![a, a] = 0 := fun a =>
    (exteriorPower.ιMulti K 2).map_eq_zero_of_eq ![a, a] (i := 0) (j := 1) (by simp) (by decide)
  let W2 : V →ₗ[K] V →ₗ[K] ⋀[K]^2 V := LinearMap.mk₂ K (fun a b => exteriorPower.ιMulti K 2 ![a, b])
    (fun a a' b => by
      have h := (exteriorPower.ιMulti K 2 (M := V)).map_update_add ![a, b] 0 a a'
      have e : ∀ x : V, Function.update (![a, b] : Fin 2 → V) 0 x = ![x, b] := by
        intro x; funext k; fin_cases k <;> simp
      simpa only [e] using h)
    (fun c a b => by
      have h := (exteriorPower.ιMulti K 2 (M := V)).map_update_smul ![a, b] 0 c a
      have e : ∀ x : V, Function.update (![a, b] : Fin 2 → V) 0 x = ![x, b] := by
        intro x; funext k; fin_cases k <;> simp
      simpa only [e] using h)
    (fun a b b' => by
      have h := (exteriorPower.ιMulti K 2 (M := V)).map_update_add ![a, b] 1 b b'
      have e : ∀ x : V, Function.update (![a, b] : Fin 2 → V) 1 x = ![a, x] := by
        intro x; funext k; fin_cases k <;> simp
      simpa only [e] using h)
    (fun c a b => by
      have h := (exteriorPower.ιMulti K 2 (M := V)).map_update_smul ![a, b] 1 c b
      have e : ∀ x : V, Function.update (![a, b] : Fin 2 → V) 1 x = ![a, x] := by
        intro x; funext k; fin_cases k <;> simp
      simpa only [e] using h)
  have hid : g - g.flip = W2 := by
    refine bK.ext fun i => bK.ext fun j => ?_
    show g (bK i) (bK j) - g (bK j) (bK i) = exteriorPower.ιMulti K 2 ![bK i, bK j]
    rw [hg, hg]
    rcases lt_trichotomy i j with h | h | h
    · rw [if_pos h, if_neg (lt_asymm h), sub_zero]
    · subst h; rw [if_neg (lt_irrefl _), sub_zero, hself]
    · rw [if_neg (lt_asymm h), if_pos h, zero_sub, hswap (bK i) (bK j), neg_neg]
  -- the cross term on V × V
  let β : (V × V) →ₗ[K] (V × V) →ₗ[K] TensorProduct K V V :=
    (TensorProduct.mk K V V).compl₁₂ (LinearMap.fst K V V) (LinearMap.snd K V V)
      - ((TensorProduct.mk K V V).compl₁₂ (LinearMap.fst K V V) (LinearMap.snd K V V)).flip
  have hβ : ∀ x y : V × V, β x y = x.1 ⊗ₜ[K] y.2 - y.1 ⊗ₜ[K] x.2 := fun x y => rfl
  let βa : (V × V) [⋀^Fin 2]→ₗ[K] TensorProduct K V V :=
    { toFun := fun m => β (m 0) (m 1)
      map_update_add' := fun m i x y => by
        fin_cases i <;> simp [map_add, LinearMap.add_apply]
      map_update_smul' := fun m i c x => by
        fin_cases i <;> simp [map_smul, LinearMap.smul_apply]
      map_eq_zero_of_eq' := fun m i j h hij => by
        have h01 : m 0 = m 1 := by
          fin_cases i <;> fin_cases j <;> first | exact absurd rfl hij | exact h | exact h.symm
        show β (m 0) (m 1) = 0
        rw [h01, hβ, sub_self] }
  let L : ⋀[K]^2 (V × V) →ₗ[K] TensorProduct K V V := exteriorPower.alternatingMapLinearEquiv βa
  have hL : ∀ (f : V →ₗ[K] V × V) (a : Fin 2 → V),
      L (exteriorPower.map 2 f (exteriorPower.ιMulti K 2 a)) = β (f (a 0)) (f (a 1)) := by
    intro f a
    rw [exteriorPower.map_apply_ιMulti]
    exact exteriorPower.alternatingMapLinearEquiv_apply_ιMulti βa _
  -- push the hypothesis to V × V along (r₁, r₂)
  have hp : (LinearMap.prod r₁ r₂) ∘ₗ p = LinearMap.inl K V V := by
    ext x
    · have := LinearMap.congr_fun h11 x; simpa using this
    · have := LinearMap.congr_fun h21 x; simpa using this
  have hq : (LinearMap.prod r₁ r₂) ∘ₗ q = LinearMap.inr K V V := by
    ext x
    · have := LinearMap.congr_fun h12 x; simpa using this
    · have := LinearMap.congr_fun h22 x; simpa using this
  have hpq : (LinearMap.prod r₁ r₂) ∘ₗ (p + q) = LinearMap.inl K V V + LinearMap.inr K V V := by
    rw [LinearMap.comp_add, hp, hq]
  have ht' := congrArg (exteriorPower.map 2 (LinearMap.prod r₁ r₂)) ht
  rw [map_add] at ht'
  simp only [← LinearMap.comp_apply, ← exteriorPower.map_comp] at ht'
  rw [hp, hq, hpq] at ht'
  have hLt := congrArg L ht'
  rw [map_add] at hLt
  -- evaluate L ∘ map on a linear basis of generators
  have hlin : ∀ s : ⋀[K]^2 V,
      L (exteriorPower.map 2 (LinearMap.inl K V V + LinearMap.inr K V V) s)
        - (L (exteriorPower.map 2 (LinearMap.inl K V V) s) + L (exteriorPower.map 2 (LinearMap.inr K V V) s))
      = exteriorPower.alternatingMapLinearEquiv
          (show V [⋀^Fin 2]→ₗ[K] TensorProduct K V V from
            βa.compLinearMap (LinearMap.inl K V V + LinearMap.inr K V V)) s := by
    intro s
    have : (L ∘ₗ exteriorPower.map 2 (LinearMap.inl K V V + LinearMap.inr K V V))
        - (L ∘ₗ exteriorPower.map 2 (LinearMap.inl K V V) + L ∘ₗ exteriorPower.map 2 (LinearMap.inr K V V))
        = exteriorPower.alternatingMapLinearEquiv (βa.compLinearMap (LinearMap.inl K V V + LinearMap.inr K V V)) := by
      refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
      simp only [LinearMap.compAlternatingMap_apply, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply, hL,
        exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      show _ = β ((LinearMap.inl K V V + LinearMap.inr K V V) (a 0)) ((LinearMap.inl K V V + LinearMap.inr K V V) (a 1))
      simp [hβ]
    exact LinearMap.congr_fun this s
  have h0 : exteriorPower.alternatingMapLinearEquiv
      (βa.compLinearMap (LinearMap.inl K V V + LinearMap.inr K V V)) t = 0 := by
    rw [← hlin t, hLt, sub_self]
  -- antisymmetrisation has the left inverse g
  have hinv : (TensorProduct.lift g) ∘ₗ (exteriorPower.alternatingMapLinearEquiv
      (βa.compLinearMap (LinearMap.inl K V V + LinearMap.inr K V V))) = LinearMap.id := by
    refine exteriorPower.linearMap_ext (AlternatingMap.ext fun a => ?_)
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
      LinearMap.id_coe, id_eq]
    have e : βa.compLinearMap (LinearMap.inl K V V + LinearMap.inr K V V) a = a 0 ⊗ₜ[K] a 1 - a 1 ⊗ₜ[K] a 0 := by
      show β ((LinearMap.inl K V V + LinearMap.inr K V V) (a 0)) ((LinearMap.inl K V V + LinearMap.inr K V V) (a 1)) = _
      simp [hβ]
    rw [e, map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul]
    have := LinearMap.congr_fun (LinearMap.congr_fun hid (a 0)) (a 1)
    have ha : (![a 0, a 1] : Fin 2 → V) = a := by funext k; fin_cases k <;> rfl
    calc g (a 0) (a 1) - g (a 1) (a 0) = W2 (a 0) (a 1) := this
      _ = exteriorPower.ιMulti K 2 a := by show exteriorPower.ιMulti K 2 ![a 0, a 1] = _; rw [ha]
  have := LinearMap.congr_fun hinv t
  rw [LinearMap.comp_apply, h0, map_zero] at this
  exact this.symm

