-- Prove2me | solution 1 for GlobalTheory.evCot_of_univDer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:38:05.094719+00:00
-- url     : https://prove2.me/submissions/977b8347-afda-4fa9-af11-8ebc2ad9b3fe

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvCotStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvCotOfUnivDer

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
open GlobalTheory
open TensorProduct IsLocalRing Matrix
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), ∃ δ : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ _root_.ReciprocityTheory.PGsh.Up.LieDualModP p (Tw.O : Type) g,
    (∀ o f, δ ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • δ f) ∧ (∀ f f', δ (f * f') = (D.ptMap 0).1 f • δ f' + (D.ptMap 0).1 f' • δ f) ∧
    (∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (d : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ M),
      (∀ o f, d ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • d f) → (∀ f f', d (f * f') = (D.ptMap 0).1 f • d f' + (D.ptMap 0).1 f' • d f) →
      ∃! u : _root_.ReciprocityTheory.PGsh.Up.LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M, ∀ f, d f = u (δ f)) ∧
    ∀ (a : Oe) (α : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx (D.ptIdx 0)) (D.fin.AAx (D.ptIdx 0))), α.comp (D.fin.sO (D.ptIdx 0)) = (D.fin.sO (D.ptIdx 0)) →
      B.map α (D.fin.y (D.ptIdx 0)) = (D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)) ⟨(D.fin.y (D.ptIdx 0)), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.fin.y_p _)⟩ : B.G (D.fin.AAx (D.ptIdx 0))) →
      ∀ f (l : Fin g → (Tw.O : Type)), δ f = Submodule.Quotient.mk l → δ (α.1 f) = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvCotStatement D) := by
  intro hU R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvCotStatement
  intro C _ _ hinj
  classical
  letI inst : ∀ i, Algebra Tw.O.carrier (D.fin.AAx i).carrier := fun i =>
    ((D.fin.sO i).1 : Tw.O.carrier →+* (D.fin.AAx i).carrier).toAlgebra
  have hspec : ∀ t, (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := fun t => by
    have h := (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) (_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (D.pt_p t)).choose_spec.choose_spec
    exact ⟨h.1, h.2.1⟩
  have hsec : ∀ t c, (D.ptMap t).1 ((D.fin.sO (D.ptIdx t)).1 c) = c := fun t c =>
    congrArg (fun φ : _root_.ReciprocityTheory.PGsh.LHom Tw.O Tw.O => φ.1 c) (hspec t).1
  let ev : ∀ t : _root_.ReciprocityTheory.PGsh.Up.Nb p g, (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] Tw.O.carrier := fun t =>
    { toRingHom := ((D.ptMap t).1 : (D.fin.AAx (D.ptIdx t)).carrier →+* Tw.O.carrier).comp
        (Pi.evalRingHom _ (D.ptIdx t))
      commutes' := fun o => hsec t o }
  let Ψ : (∀ i, (D.fin.AAx i).carrier) →ₐ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → Tw.O.carrier) :=
    Pi.algHom _ _ ev
  let f : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] (_root_.ReciprocityTheory.PGsh.Up.Nb p g → C) :=
    (Algebra.linearMap Tw.O.carrier C).compLeft (_root_.ReciprocityTheory.PGsh.Up.Nb p g) ∘ₗ Ψ.toLinearMap
  have hf : ∀ F x, f F x = algebraMap _ C ((D.ptMap x).1 (F (D.ptIdx x))) := fun F x => rfl
  have hfmul : ∀ F G, f (F * G) = f F * f G := fun F G => by
    funext x; simp only [hf, Pi.mul_apply, map_mul]
  have himg : D.evImg C = LinearMap.range f := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg _root_.ReciprocityTheory.PGsh.Be2.Dat.evAll
    change Submodule.span _ (Set.range ⇑f) = _
    rw [← LinearMap.coe_range, Submodule.span_eq]
  have hinjΨ : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    funext i
    apply D.fin.sep i
    intro φ hφ
    have hz : p • B.map φ (D.fin.y i) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
    obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
    have ht' : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t = B.map φ (D.fin.y i) := congrArg Subtype.val ht
    obtain ⟨i0, φ0, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ hz
    obtain ⟨hi, hφ0⟩ := huniq i φ hφ rfl
    obtain ⟨hi', hψ0⟩ := huniq (D.ptIdx t) (D.ptMap t) (hspec t).1 ((hspec t).2.trans ht')
    subst hi
    have key : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), j = i → HEq ψ φ →
        ψ.1 (F j) = φ.1 (F i) := by
      rintro j ψ rfl h
      rw [eq_of_heq h]
    exact (key _ _ hi' (hψ0.trans hφ0.symm)).symm.trans (congrFun hF t)
  have finj : Function.Injective f := fun F G h =>
    hinjΨ (funext fun x => hinj (congrFun h x))
  obtain ⟨δ, hδlin, hδder, hδuniv, hδeq⟩ := hU D
  clear hU
  have hπs : ∀ c, (D.ptMap 0).1 ((D.fin.sO (D.ptIdx 0)).1 c) = c := hsec 0
  have hδ1 : δ 1 = 0 := by
    have h := hδder 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h2 : δ 1 + δ 1 = δ 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h2
  have hδs : ∀ c, δ ((D.fin.sO (D.ptIdx 0)).1 c) = 0 := fun c => by
    have h := hδlin c 1
    rw [mul_one, hδ1, smul_zero] at h
    exact h

  have hδsurj : Function.Surjective δ := by
    let N : Submodule Tw.O.carrier (_root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g) :=
      { carrier := Set.range δ
        add_mem' := by rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩; exact ⟨x + y, map_add δ x y⟩
        zero_mem' := ⟨0, map_zero δ⟩
        smul_mem' := by rintro c _ ⟨x, rfl⟩; exact ⟨_, hδlin c x⟩ }
    let d : (D.fin.AAx (D.ptIdx 0)).carrier →+ (_root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g ⧸ N) :=
      N.mkQ.toAddMonoidHom.comp δ
    obtain ⟨u, -, huniq⟩ := hδuniv _ d
      (fun o x => by simp only [d, AddMonoidHom.comp_apply, hδlin]; exact map_smul N.mkQ o (δ x))
      (fun x y => by
        simp only [d, AddMonoidHom.comp_apply, hδder]
        exact (map_add N.mkQ _ _).trans (by rw [map_smul, map_smul]; rfl))
    have h1 := huniq N.mkQ (fun x => rfl)
    have h2 := huniq 0 (fun x => by
      show N.mkQ (δ x) = 0
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact ⟨x, rfl⟩)
    intro q
    have hq : N.mkQ q = 0 := by rw [h1.trans h2.symm]; rfl
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hq
    exact hq
  have hmemA : ∀ F, f F ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) ↔ (D.ptMap 0).1 (F (D.ptIdx 0)) = 0 := fun F => by
    unfold _root_.ReciprocityTheory.PGsh.L2.augIdeal
    rw [Submodule.mem_inf, LinearMap.mem_ker, LinearMap.proj_apply, hf]
    refine ⟨fun h => hinj (h.2.trans (map_zero _).symm), fun h => ⟨?_, by rw [h, map_zero]⟩⟩
    rw [himg]; exact ⟨F, rfl⟩
  have hle : _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) ≤ LinearMap.range f := fun h hh => by
    unfold _root_.ReciprocityTheory.PGsh.L2.augIdeal at hh; rw [← himg]; exact (Submodule.mem_inf.1 hh).1
  let e := LinearEquiv.ofInjective f finj
  let Δ : (∀ i, (D.fin.AAx i).carrier) →ₗ[Tw.O.carrier] _root_.ReciprocityTheory.PGsh.Up.LieDualModP p Tw.O.carrier g :=
    { toFun := fun F => δ (F (D.ptIdx 0))
      map_add' := fun F G => map_add δ _ _
      map_smul' := fun c F => hδlin c _ }
  let φ := Δ ∘ₗ (e.symm : LinearMap.range f →ₗ[Tw.O.carrier] _) ∘ₗ Submodule.inclusion hle
  have hφ : ∀ F (hF : f F ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)), φ ⟨f F, hF⟩ = δ (F (D.ptIdx 0)) := fun F hF => by
    have he : e.symm ⟨f F, hle hF⟩ = F := e.symm_apply_eq.2 (Subtype.ext (by simp [e]))
    show Δ (e.symm ⟨f F, hle hF⟩) = _
    rw [he]; rfl
  refine ⟨φ, ?_, ?_, ?_⟩
  · intro q
    obtain ⟨x, rfl⟩ := hδsurj q
    have hx' : (D.ptMap 0).1 (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x)) = 0 := by
      rw [map_sub, hπs, sub_self]
    have hmem : f (Pi.single (D.ptIdx 0) (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x))) ∈
        _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) := (hmemA _).2 (by rw [Pi.single_eq_same]; exact hx')
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [hφ, Pi.single_eq_same, map_sub, hδs, sub_zero]
  · ext ⟨h, hh⟩
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply]
    obtain ⟨F, rfl⟩ : h ∈ LinearMap.range f := hle hh
    rw [hφ F hh]
    constructor
    · intro h0
      let π0 : (D.fin.AAx (D.ptIdx 0)).carrier →ₗ[Tw.O.carrier] Tw.O.carrier :=
        { toFun := (D.ptMap 0).1
          map_add' := map_add _
          map_smul' := fun c x => by
            show (D.ptMap 0).1 ((D.fin.sO (D.ptIdx 0)).1 c * x) = c * (D.ptMap 0).1 x
            rw [map_mul, hπs] }
      let I := LinearMap.ker π0
      let J : Submodule Tw.O.carrier I := Submodule.comap I.subtype
        (Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b})
      have hsub : ∀ x, x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x) ∈ I := fun x => by
        rw [LinearMap.mem_ker]
        show (D.ptMap 0).1 (x - _) = 0
        rw [map_sub, hπs, sub_self]
      let d : (D.fin.AAx (D.ptIdx 0)).carrier →+ (I ⧸ J) :=
        { toFun := fun x => Submodule.Quotient.mk ⟨_, hsub x⟩
          map_zero' := by
            rw [← Submodule.Quotient.mk_zero]; congr 1; apply Subtype.ext
            simp only [map_zero, sub_zero, ZeroMemClass.coe_zero]
          map_add' := fun x y => by
            rw [← Submodule.Quotient.mk_add]; congr 1; apply Subtype.ext
            simp only [map_add, Submodule.coe_add]; abel }
      obtain ⟨u, hu, -⟩ := hδuniv (I ⧸ J) d
        (fun o x => by
          show Submodule.Quotient.mk _ = o • Submodule.Quotient.mk _
          rw [← Submodule.Quotient.mk_smul]; congr 1; apply Subtype.ext
          show _ = (D.fin.sO (D.ptIdx 0)).1 o * (x - _)
          simp only [map_mul, hπs, mul_sub])
        (fun x y => by
          show Submodule.Quotient.mk _ = (D.ptMap 0).1 x • Submodule.Quotient.mk _ +
            (D.ptMap 0).1 y • Submodule.Quotient.mk _
          rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul,
            ← Submodule.Quotient.mk_add, Submodule.Quotient.eq, Submodule.mem_comap]
          have hm : (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x)) *
              (y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y)) ∈
              Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b} :=
            Submodule.subset_span ⟨_, hsub x, _, hsub y, rfl⟩
          convert hm using 1
          show x * y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 (x * y)) -
            ((D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x) * (y - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y)) +
            (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 y) * (x - (D.fin.sO (D.ptIdx 0)).1 ((D.ptMap 0).1 x))) = _
          rw [map_mul, map_mul]
          ring)
      have hπF : (D.ptMap 0).1 (F (D.ptIdx 0)) = 0 := (hmemA F).1 hh
      have hx : F (D.ptIdx 0) ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b} := by
        have h1 := hu (F (D.ptIdx 0))
        rw [h0, map_zero] at h1
        have h3 := Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h1)
        simpa [hπF] using h3
      have hlift : ∀ z ∈ Submodule.span Tw.O.carrier {z | ∃ a ∈ I, ∃ b ∈ I, z = a * b},
          f (Pi.single (D.ptIdx 0) z) ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)) := by
        intro z hz
        unfold _root_.ReciprocityTheory.PGsh.Up.sqIdeal
        induction hz using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨a, ha, b, hb, rfl⟩ := hz
          exact Submodule.subset_span ⟨f (Pi.single _ a), (hmemA _).2 (by rw [Pi.single_eq_same]; exact ha),
            f (Pi.single _ b), (hmemA _).2 (by rw [Pi.single_eq_same]; exact hb),
            by rw [Pi.single_mul, hfmul]⟩
        | zero => rw [Pi.single_zero, map_zero]; exact zero_mem _
        | add x y _ _ hx hy => rw [Pi.single_add, map_add]; exact add_mem hx hy
        | smul c x _ hx =>
          have hs : (Pi.single (D.ptIdx 0) (c • x) : ∀ i, (D.fin.AAx i).carrier) =
              c • (Pi.single (D.ptIdx 0) x : ∀ i, (D.fin.AAx i).carrier) := by
            funext j
            by_cases hj : j = D.ptIdx 0
            · subst hj; simp
            · simp [Pi.single_eq_of_ne hj]
          rw [hs, map_smul]; exact Submodule.smul_mem _ c hx
      let G := F - Pi.single (D.ptIdx 0) (F (D.ptIdx 0))
      let E : ∀ i, (D.fin.AAx i).carrier := 1 - Pi.single (D.ptIdx 0) 1
      have hG : E * G = G := by
        funext j
        by_cases hj : j = D.ptIdx 0
        · subst hj; simp [E, G]
        · simp [E, G, Pi.single_eq_of_ne hj]
      have hEmem : f E ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) := (hmemA E).2 (by simp [E])
      have hGmem : f G ∈ _root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C) := (hmemA G).2 (by simp [G])
      have hF : f F = f (Pi.single (D.ptIdx 0) (F (D.ptIdx 0))) + f G := by
        rw [← map_add]; congr 1; simp [G]
      show f F ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C))
      rw [hF]
      refine add_mem (hlift _ hx) ?_
      rw [← hG, hfmul]
      unfold _root_.ReciprocityTheory.PGsh.Up.sqIdeal
      exact Submodule.subset_span ⟨_, hEmem, _, hGmem, rfl⟩
    · intro hsq
      have P : ∀ h ∈ _root_.ReciprocityTheory.PGsh.Up.sqIdeal (_root_.ReciprocityTheory.PGsh.L2.augIdeal (D.evImg C)), ∃ F', f F' = h ∧ δ (F' (D.ptIdx 0)) = 0 := by
        intro h hh'
        unfold _root_.ReciprocityTheory.PGsh.Up.sqIdeal at hh'
        induction hh' using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨h1, hh1, h2, hh2, rfl⟩ := hz
          obtain ⟨F1, rfl⟩ := hle hh1
          obtain ⟨F2, rfl⟩ := hle hh2
          refine ⟨F1 * F2, hfmul _ _, ?_⟩
          rw [Pi.mul_apply, hδder, (hmemA F1).1 hh1, (hmemA F2).1 hh2, zero_smul, zero_smul, add_zero]
        | zero => exact ⟨0, map_zero f, by rw [Pi.zero_apply, map_zero]⟩
        | add x y _ _ hx hy =>
          obtain ⟨F1, rfl, h1⟩ := hx
          obtain ⟨F2, rfl, h2⟩ := hy
          exact ⟨F1 + F2, map_add f _ _, by rw [Pi.add_apply, map_add, h1, h2, add_zero]⟩
        | smul c x _ hx =>
          obtain ⟨F1, rfl, h1⟩ := hx
          refine ⟨c • F1, map_smul f _ _, ?_⟩
          show δ ((D.fin.sO (D.ptIdx 0)).1 c * F1 (D.ptIdx 0)) = 0
          rw [hδlin, h1, smul_zero]
      obtain ⟨F', hF', hδF'⟩ := P _ hsq
      rw [finj hF'] at hδF'
      exact hδF'
  · intro a ⟨h1, hh1⟩ ⟨h2, hh2⟩ l hrel hl
    obtain ⟨F1, rfl⟩ : h1 ∈ LinearMap.range f := hle hh1
    obtain ⟨F2, rfl⟩ : h2 ∈ LinearMap.range f := hle hh2
    rw [hφ] at hl ⊢
    have hτ : ∀ k, p • D.L.τ k 0 = 0 := fun k => by simpa using D.L.τ_tors k 0
    have hmod : ∀ (x : B.G Tw.O) (n : ℕ), p • x = 0 → ((n : ZMod p).val) • x = n • x := by
      intro x n hx
      rw [ZMod.val_natCast]
      conv_rhs => rw [← Nat.mod_add_div n p]
      rw [add_nsmul, mul_comm, ← smul_smul, hx, smul_zero, add_zero]
    have hact : ∀ (s : _root_.ReciprocityTheory.PGsh.Up.TT p g) hp,
        (↑(D.A.act a Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) ⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), hp⟩) : B.G Tw.O) =
          _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s)) := by
      intro s hp
      have hsplit : (⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), hp⟩ : ↥(_root_.ReciprocityTheory.PGsh.Be2.torP B p Tw.O)) =
          ∑ j, (PadicInt.toZMod (s j)).val • ⟨D.L.τ j 0, (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (hτ j)⟩ := by
        apply Subtype.ext
        simp [_root_.ReciprocityTheory.PGsh.Be2.ptOf, _root_.ReciprocityTheory.PGsh.Up.red]
      rw [hsplit, map_sum]
      simp only [map_nsmul]
      push_cast
      simp only [D.L.ρ_spec]
      simp only [_root_.ReciprocityTheory.PGsh.Be2.ptOf, _root_.ReciprocityTheory.PGsh.Up.red, Matrix.mulVec, dotProduct, map_sum, map_mul, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hc : (∑ j, PadicInt.toZMod (D.H.ρ a k j) * PadicInt.toZMod (s j)) =
          ((∑ j, (PadicInt.toZMod (D.H.ρ a k j)).val * (PadicInt.toZMod (s j)).val : ℕ) : ZMod p) := by
        simp only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val]
      rw [hc, hmod _ _ (hτ k), Finset.sum_smul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_comm]
    have tr : ∀ (G : ∀ i, (D.fin.AAx i).carrier) (j j' : D.fin.ι) (χ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O)
        (χ' : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j') Tw.O), j = j' → HEq χ χ' → χ.1 (G j) = χ'.1 (G j') := by
      rintro G j j' χ χ' rfl h
      rw [eq_of_heq h]
    have hpt : ∀ (j : D.fin.ι) (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O), ψ.comp (D.fin.sO j) = _root_.ReciprocityTheory.PGsh.LHom.id _ →
        ∀ t, B.map ψ (D.fin.y j) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t → D.ptIdx t = j ∧ HEq (D.ptMap t) ψ := by
      intro j ψ hψ t ht
      obtain ⟨i1, φ1, -, -, huniq⟩ := D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ (D.pt_p t)
      obtain ⟨e1, e2⟩ := huniq j ψ hψ ht
      obtain ⟨e3, e4⟩ := huniq _ _ (hspec t).1 (hspec t).2
      exact ⟨e3.trans e1.symm, e4.trans e2.symm⟩
    have hyt := (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).1 ((D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)))
        ⟨D.fin.y (D.ptIdx 0), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.fin.y_p _)⟩).2
    obtain ⟨i, φa, hφs, hφz, -⟩ := D.fin.univ _ (D.fin.sO (D.ptIdx 0)) _ hyt
    have hcomp : ∀ (ψ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx (D.ptIdx 0)) Tw.O), ψ.comp (D.fin.sO (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.LHom.id _ →
        ∀ s, B.map ψ (D.fin.y (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s) →
        (ψ.comp φa).comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id _ ∧
          B.map (ψ.comp φa) (D.fin.y i) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s)) := by
      intro ψ hψ s hs
      refine ⟨?_, ?_⟩
      · show ψ.comp (φa.comp (D.fin.sO i)) = _
        rw [hφs, hψ]
      · rw [B.map_comp, hφz, D.A.act_nat a (D.fin.sO _) (_root_.ReciprocityTheory.PGsh.LHom.id _) ψ hψ]
        have e1 : (⟨B.map ψ (D.fin.y (D.ptIdx 0)), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (by rw [hs]; exact D.pt_p _)⟩ :
            ↥(_root_.ReciprocityTheory.PGsh.Be2.torP B p Tw.O)) = ⟨_root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s), (_root_.ReciprocityTheory.PGsh.Be2.mem_torP B p _).2 (D.pt_p _)⟩ :=
          Subtype.ext hs
        rw [e1]
        exact hact s _
    have hVW0 : _root_.ReciprocityTheory.PGsh.Up.red p g 0 = 0 := by funext k; simp [_root_.ReciprocityTheory.PGsh.Up.red]
    have h00 := hcomp (D.ptMap 0) (hspec 0).1 0 (by rw [hVW0]; exact (hspec 0).2)
    rw [Matrix.mulVec_zero, hVW0] at h00
    obtain ⟨hi, -⟩ := hpt i _ h00.1 0 h00.2
    subst hi
    have hmain : φa.1 (F1 (D.ptIdx 0)) = F2 (D.ptIdx 0) := by
      rw [← sub_eq_zero]
      apply D.fin.sep
      intro ψ hψ
      have hz : p • B.map ψ (D.fin.y (D.ptIdx 0)) = 0 := by rw [← map_nsmul, D.fin.y_p, map_zero]
      obtain ⟨t, ht⟩ := D.L.τ_basis.2 ⟨_, hz⟩
      let s : _root_.ReciprocityTheory.PGsh.Up.TT p g := fun k => ((t k).val : ℤ_[p])
      have hts : _root_.ReciprocityTheory.PGsh.Up.red p g s = t := by funext k; simp [s, _root_.ReciprocityTheory.PGsh.Up.red]
      have hs : B.map ψ (D.fin.y (D.ptIdx 0)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (_root_.ReciprocityTheory.PGsh.Up.red p g s) := by
        rw [hts]; exact (congrArg Subtype.val ht).symm
      obtain ⟨c1, c2⟩ := hcomp ψ hψ s hs
      obtain ⟨j1, k1⟩ := hpt _ _ c1 _ c2
      obtain ⟨j2, k2⟩ := hpt _ _ hψ _ hs
      have hr : f F2 (_root_.ReciprocityTheory.PGsh.Up.red p g s) = f F1 (_root_.ReciprocityTheory.PGsh.Up.red p g (D.H.ρ a *ᵥ s)) := hrel s
      rw [hf, hf] at hr
      have hr' := hinj hr
      rw [tr F2 _ _ _ _ j2 k2, tr F1 _ _ _ _ j1 k1] at hr'
      show ψ.1 (φa.1 (F1 (D.ptIdx 0)) - F2 (D.ptIdx 0)) = 0
      rw [map_sub, sub_eq_zero]
      exact hr'.symm
    rw [← hmain]
    exact hδeq a φa hφs hφz _ l hl
end _root_.GlobalTheory
end GlobalTheory
