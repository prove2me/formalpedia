-- Prove2me | solution 1 for NumberField.ArchIdele.exists_addEquiv_coind_localUnits_transportUnits_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/9a73d422-9fcd-50a6-94f7-15dfbc70ed6a

import Mathlib
import Definitions.Def_NumberField_ArchimedeanIdeleModule
import Definitions.Def_NumberField_InfinitePlaceTransport
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_one
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_trans_transport
import Theorems.Thm_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply

set_option autoImplicit false

namespace P2mS26AHF

open NumberField NumberField.InfinitePlaceTransport
open scoped NumberField.InfPlaceDecomp

section general

variable {E K : Type} [Field E] [Field K] [Algebra E K]

theorem comap_smul_algebraMap (σ : K ≃ₐ[E] K) (w : InfinitePlace K) :
    (σ • w).comap (algebraMap E K) = w.comap (algebraMap E K) := by
  rw [InfinitePlace.smul_eq_comap, ← InfinitePlace.comap_comp]
  congr 1
  exact RingHom.ext fun x => σ.symm.commutes x

theorem transportUnits_congr {σ τ : K ≃ₐ[E] K} (e : σ = τ) {w w' : InfinitePlace K} (h₁ : σ • w = w') (h₂ : τ • w = w')
    (u : (w.Completion)ˣ) : transportUnits σ h₁ u = transportUnits τ h₂ u := by
  subst e; rfl

theorem transportUnits_trans (σ τ : K ≃ₐ[E] K) {w w' w'' : InfinitePlace K} (h₁ : τ • w = w') (h₂ : σ • w' = w'')
    (h₃ : (σ * τ) • w = w'') (u : (w.Completion)ˣ) :
    transportUnits σ h₂ (transportUnits τ h₁ u) = transportUnits (σ * τ) h₃ u := by
  ext : 1
  change transport σ h₂ (transport τ h₁ (u : w.Completion)) = transport (σ * τ) h₃ (u : w.Completion)
  rw [← NumberField.InfinitePlaceTransport.transport_trans_transport E K σ τ h₁ h₂ h₃]
  rfl

theorem transportUnits_one {w : InfinitePlace K} (h : (1 : K ≃ₐ[E] K) • w = w) (u : (w.Completion)ˣ) :
    transportUnits (1 : K ≃ₐ[E] K) h u = u := by
  ext : 1
  change transport (1 : K ≃ₐ[E] K) h (u : w.Completion) = u
  rw [NumberField.InfinitePlaceTransport.transport_one E K w h]
  rfl

theorem transportUnits_eq_smul {w : InfinitePlace K} (d : InfPlaceDecomp.decomp E K w) (h : (d : K ≃ₐ[E] K) • w = w)
    (u : (w.Completion)ˣ) : transportUnits (d : K ≃ₐ[E] K) h u = d • u := by
  ext : 1
  change transport (d : K ≃ₐ[E] K) h (u : w.Completion) = ((d • u : (w.Completion)ˣ) : w.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_eq_actRingEquiv E K w d h, InfPlaceDecomp.coe_smul_units,
    InfPlaceDecomp.smul_def]

end general

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

abbrev Idx (v : InfinitePlace E) : Type := {w : InfinitePlace K // w.comap (algebraMap E K) = v}

noncomputable abbrev Cv (v : InfinitePlace E) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.coind (InfPlaceDecomp.decomp E K (ArchIdele.above E K v)).subtype (InfPlaceDecomp.localUnits E K (ArchIdele.above E K v))

variable {E K}
variable (v : InfinitePlace E)

noncomputable def fval (f : Cv E K v) (x : K ≃ₐ[E] K) : ((ArchIdele.above E K v).Completion)ˣ := Additive.toMul (f.1 x)

theorem fval_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (x : K ≃ₐ[E] K) : fval v ((Cv E K v).ρ g f) x = fval v f (x * g) := rfl

theorem fval_add (f₁ f₂ : Cv E K v) (x : K ≃ₐ[E] K) : fval v (f₁ + f₂) x = fval v f₁ x * fval v f₂ x := rfl

theorem coind_mem (f : Cv E K v) (d : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) (x : K ≃ₐ[E] K) :
    fval v f ((d : K ≃ₐ[E] K) * x) = d • fval v f x :=
  congrArg Additive.toMul ((Representation.mem_coindV _ _ _).1 f.2 d x)

omit [NumberField E] [NumberField K] in

theorem transportUnits_congr_idx (u : Π w : Idx E K v, (w.1.Completion)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (σ : K ≃ₐ[E] K) {t : InfinitePlace K} (h₁ : σ • i₁.1 = t) (h₂ : σ • i₂.1 = t) :
    transportUnits σ h₁ (u i₁) = transportUnits σ h₂ (u i₂) := by
  subst e; rfl

omit [NumberField E] [NumberField K] in
theorem transportUnits_one_idx (u : Π w : Idx E K v, (w.1.Completion)ˣ) {i₁ i₂ : Idx E K v} (e : i₁ = i₂)
    (h : (1 : K ≃ₐ[E] K) • i₁.1 = i₂.1) : transportUnits (1 : K ≃ₐ[E] K) h (u i₁) = u i₂ := by
  subst e
  exact transportUnits_one h (u i₁)

theorem indep (f : Cv E K v) (x y : K ≃ₐ[E] K) (w : InfinitePlace K)
    (hx : x⁻¹ • ArchIdele.above E K v = w) (hy : y⁻¹ • ArchIdele.above E K v = w) :
    transportUnits y⁻¹ hy (fval v f y) = transportUnits x⁻¹ hx (fval v f x) := by
  have hd : y * x⁻¹ ∈ InfPlaceDecomp.decomp E K (ArchIdele.above E K v) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul, hx, ← hy, smul_inv_smul]
  obtain ⟨d, rfl⟩ : ∃ d : InfPlaceDecomp.decomp E K (ArchIdele.above E K v), (d : K ≃ₐ[E] K) * x = y :=
    ⟨⟨y * x⁻¹, hd⟩, inv_mul_cancel_right y x⟩
  have hd1 : ((d⁻¹ : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) : K ≃ₐ[E] K) • ArchIdele.above E K v =
      ArchIdele.above E K v := (d⁻¹).2
  rw [coind_mem, transportUnits_congr (show ((d : K ≃ₐ[E] K) * x)⁻¹ =
        x⁻¹ * ((d⁻¹ : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) : K ≃ₐ[E] K) by rw [mul_inv_rev]; rfl) hy
      (by rw [mul_smul]; exact (congrArg (x⁻¹ • ·) hd1).trans hx),
    ← transportUnits_trans x⁻¹ ((d⁻¹ : InfPlaceDecomp.decomp E K (ArchIdele.above E K v)) : K ≃ₐ[E] K) hd1 hx,
    transportUnits_eq_smul, inv_smul_smul]

theorem mem_idx (x : K ≃ₐ[E] K) : (x⁻¹ • ArchIdele.above E K v).comap (algebraMap E K) = v :=
  (comap_smul_algebraMap x⁻¹ _).trans (ArchIdele.comap_above E K v)

noncomputable def bwdFun (u : Π w : Idx E K v, (w.1.Completion)ˣ) : (K ≃ₐ[E] K) → Additive ((ArchIdele.above E K v).Completion)ˣ :=
  fun x => Additive.ofMul (transportUnits x (smul_inv_smul x (ArchIdele.above E K v)) (u ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩))

theorem bwdFun_apply (u : Π w : Idx E K v, (w.1.Completion)ˣ) (x : K ≃ₐ[E] K) :
    Additive.toMul (bwdFun v u x) = transportUnits x (smul_inv_smul x (ArchIdele.above E K v)) (u ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩) := rfl

theorem bwdFun_mem (u : Π w : Idx E K v, (w.1.Completion)ˣ) :
    bwdFun v u ∈ Representation.coindV (InfPlaceDecomp.decomp E K (ArchIdele.above E K v)).subtype
      (InfPlaceDecomp.localUnits E K (ArchIdele.above E K v)).ρ := by
  refine (Representation.mem_coindV _ _ _).2 fun d x => ?_
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v u ((d : K ≃ₐ[E] K) * x)) = d • Additive.toMul (bwdFun v u x)
  have hidx : (⟨((d : K ≃ₐ[E] K) * x)⁻¹ • ArchIdele.above E K v, mem_idx v ((d : K ≃ₐ[E] K) * x)⟩ : Idx E K v) =
      ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩ := by
    apply Subtype.ext
    change ((d : K ≃ₐ[E] K) * x)⁻¹ • ArchIdele.above E K v = x⁻¹ • ArchIdele.above E K v
    rw [mul_inv_rev, mul_smul]
    exact congrArg (x⁻¹ • ·) (d⁻¹).2
  rw [bwdFun_apply, bwdFun_apply, transportUnits_congr_idx v u hidx ((d : K ≃ₐ[E] K) * x) _
      (by rw [mul_smul, smul_inv_smul]; exact d.2),
    ← transportUnits_trans (d : K ≃ₐ[E] K) x (smul_inv_smul x _) d.2, transportUnits_eq_smul]

noncomputable def bwd (u : Π w : Idx E K v, (w.1.Completion)ˣ) : Cv E K v := ⟨bwdFun v u, bwdFun_mem v u⟩

section
variable [IsGalois E K]

theorem exists_smul_eq (w : Idx E K v) : ∃ x : K ≃ₐ[E] K, x • w.1 = ArchIdele.above E K v :=
  InfinitePlace.exists_smul_eq_of_comap_eq (w.2.trans (ArchIdele.comap_above E K v).symm)

noncomputable def sel (w : Idx E K v) : K ≃ₐ[E] K := (exists_smul_eq v w).choose

theorem sel_smul (w : Idx E K v) : sel v w • w.1 = ArchIdele.above E K v := (exists_smul_eq v w).choose_spec

theorem inv_sel_smul (w : Idx E K v) : (sel v w)⁻¹ • ArchIdele.above E K v = w.1 := inv_smul_eq_of_smul_eq (sel_smul v w)

noncomputable def fwd (f : Cv E K v) : Π w : Idx E K v, (w.1.Completion)ˣ :=
  fun w => transportUnits (sel v w)⁻¹ (inv_sel_smul v w) (fval v f (sel v w))

theorem fwd_eq (f : Cv E K v) (w : Idx E K v) (y : K ≃ₐ[E] K) (hy : y • w.1 = ArchIdele.above E K v) :
    fwd v f w = transportUnits y⁻¹ (inv_smul_eq_of_smul_eq hy) (fval v f y) :=
  (indep v f y (sel v w) w.1 (inv_smul_eq_of_smul_eq hy) (inv_sel_smul v w))

theorem fwd_add (f₁ f₂ : Cv E K v) (w : Idx E K v) : fwd v (f₁ + f₂) w = fwd v f₁ w * fwd v f₂ w := by
  change transportUnits _ _ (fval v (f₁ + f₂) (sel v w)) = _
  rw [fval_add, map_mul]
  rfl

theorem fwd_ρ (g : K ≃ₐ[E] K) (f : Cv E K v) (w w' : Idx E K v) (h : g • w'.1 = w.1) :
    fwd v ((Cv E K v).ρ g f) w = transportUnits g h (fwd v f w') := by
  have hy : (sel v w * g) • w'.1 = ArchIdele.above E K v := by rw [mul_smul, h, sel_smul]
  rw [fwd_eq v f w' (sel v w * g) hy, transportUnits_trans g (sel v w * g)⁻¹ (inv_smul_eq_of_smul_eq hy) h
      (by rw [mul_inv_rev, mul_inv_cancel_left]; exact inv_sel_smul v w),
    transportUnits_congr (show g * (sel v w * g)⁻¹ = (sel v w)⁻¹ by rw [mul_inv_rev, mul_inv_cancel_left]) _ (inv_sel_smul v w)]
  rfl

theorem fwd_bwd (u : Π w : Idx E K v, (w.1.Completion)ˣ) (w : Idx E K v) : fwd v (bwd v u) w = u w := by
  have hidx : (⟨(sel v w)⁻¹ • ArchIdele.above E K v, mem_idx v (sel v w)⟩ : Idx E K v) = w := Subtype.ext (inv_sel_smul v w)
  change transportUnits (sel v w)⁻¹ (inv_sel_smul v w) (Additive.toMul (bwdFun v u (sel v w))) = u w
  rw [bwdFun_apply, transportUnits_trans (sel v w)⁻¹ (sel v w) (smul_inv_smul (sel v w) _) (inv_sel_smul v w)
      (by rw [inv_mul_cancel, one_smul]; exact inv_sel_smul v w),
    transportUnits_congr (inv_mul_cancel (sel v w)) _ (by rw [one_smul]; exact inv_sel_smul v w)]
  exact transportUnits_one_idx v u hidx _

theorem bwd_fwd (f : Cv E K v) : bwd v (fwd v f) = f := by
  apply Subtype.ext
  funext x
  apply Additive.toMul.injective
  change Additive.toMul (bwdFun v (fwd v f) x) = fval v f x
  rw [bwdFun_apply, fwd_eq v f ⟨x⁻¹ • ArchIdele.above E K v, mem_idx v x⟩ x (smul_inv_smul x _),
    transportUnits_trans x x⁻¹ _ (smul_inv_smul x _) (by rw [mul_inv_cancel, one_smul]),
    transportUnits_congr (mul_inv_cancel x) _ (one_smul _ _), transportUnits_one]

noncomputable def equiv : Cv E K v ≃+ Additive (Π w : Idx E K v, (w.1.Completion)ˣ) where
  toFun f := Additive.ofMul (fwd v f)
  invFun a := bwd v (Additive.toMul a)
  left_inv f := bwd_fwd v f
  right_inv a := congrArg Additive.ofMul (funext (fwd_bwd v (Additive.toMul a)))
  map_add' f₁ f₂ := congrArg Additive.ofMul (funext (fwd_add v f₁ f₂))

end

end P2mS26AHF

namespace P2mS26AHF

open NumberField NumberField.InfinitePlaceTransport
open scoped NumberField.InfPlaceDecomp

variable {E K : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
variable (v : InfinitePlace E)

theorem transportUnits_fwd (f : Cv E K v) (y : K ≃ₐ[E] K) (w : Idx E K v) (hy : y • w.1 = ArchIdele.above E K v) :
    transportUnits y hy (fwd v f w) = fval v f y := by
  rw [fwd_eq v f w y hy, transportUnits_trans y y⁻¹ (inv_smul_eq_of_smul_eq hy) hy (by rw [mul_inv_cancel, one_smul]),
    transportUnits_congr (mul_inv_cancel y) _ (one_smul _ _), transportUnits_one]

end P2mS26AHF

theorem solution (E K : Type) [Field E] [NumberField E]
    [Field K] [NumberField K] [Algebra E K] [IsGalois E K] (v : NumberField.InfinitePlace E) :
    ∃ e : (Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v))) ≃+
        Additive (Π w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v}, (w.1.Completion)ˣ),
      ∀ (f : Rep.coind (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)).subtype
          (NumberField.InfPlaceDecomp.localUnits E K (NumberField.ArchIdele.above E K v)))
        (y : K ≃ₐ[E] K) (w : {w : NumberField.InfinitePlace K // w.comap (algebraMap E K) = v})
        (hy : y • w.1 = NumberField.ArchIdele.above E K v),
        NumberField.InfinitePlaceTransport.transportUnits y hy (Additive.toMul (e f) w) = Additive.toMul (f.1 y) :=
  ⟨P2mS26AHF.equiv v, fun f y w hy => P2mS26AHF.transportUnits_fwd v f y w hy⟩

end S_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply
end P2MW
export P2MW.S_NumberField_ArchIdele_exists_addEquiv_coind_localUnits_transportUnits_apply (solution)
