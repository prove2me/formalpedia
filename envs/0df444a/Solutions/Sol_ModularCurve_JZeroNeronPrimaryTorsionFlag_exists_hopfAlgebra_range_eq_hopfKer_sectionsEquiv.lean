-- Prove2me | solution 1 for ModularCurve.JZeroNeronPrimaryTorsionFlag.exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7219320d-ee64-5e32-b1db-594fda4c41bf

import Mathlib
import Definitions.Def_ModularCurve_JZeroNeronPrimaryTorsionFlag
import Definitions.Def_HopfAlgebra_HopfKer
import Definitions.Def_HopfAlgebra_HopfKerHopf
import Theorems.Thm_HopfAlgebra_isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv

set_option autoImplicit false

open ModularCurve AlgebraicGeometry AlgebraicGeometry.Scheme ValuationSubring CategoryTheory
open scoped TensorProduct

noncomputable section

namespace PrimaryLayerKernelReduction

section Cocomm

variable {R : Type} [CommRing R] {H : Type} [CommRing H] [Bialgebra R H]

theorem convMul_includeLeft_includeRight_apply (h : H) :
    (WithConv.toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
        WithConv.toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)) h
      = Coalgebra.comul (R := R) h := by
  rw [AlgHom.convMul_apply]
  have hlift : Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
      (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) (fun _ _ => .all _ _)
      = AlgHom.id R (H ⊗[R] H) := by
    ext <;> simp
  simp [hlift]

theorem convMul_includeRight_includeLeft_apply (h : H) :
    (WithConv.toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) *
        WithConv.toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)) h
      = TensorProduct.comm R H H (Coalgebra.comul (R := R) h) := by
  rw [AlgHom.convMul_apply]
  have hlift : Algebra.TensorProduct.lift
      (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)
      (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) (fun _ _ => .all _ _)
      = (Algebra.TensorProduct.comm R H H : H ⊗[R] H →ₐ[R] H ⊗[R] H) := by
    ext <;> simp
  rw [hlift]
  induction (Coalgebra.comul (R := R) h) using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem isCocomm_of_convMul_comm
    (hcomm : WithConv.toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H) *
        WithConv.toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)
      = WithConv.toConv (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H) *
        WithConv.toConv (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)) :
    Coalgebra.IsCocomm R H := by
  refine ⟨?_⟩
  apply LinearMap.ext
  intro x
  have h1 := convMul_includeLeft_includeRight_apply (R := R) x
  have h2 := convMul_includeRight_includeLeft_apply (R := R) x
  rw [hcomm] at h1
  rw [h1] at h2

  change TensorProduct.comm R H H (Coalgebra.comul (R := R) x) = Coalgebra.comul (R := R) x
  exact h2.symm

theorem isCocomm_of_points_comm
    (hcomm : ∀ g₁ g₂ : WithConv (H →ₐ[R] H ⊗[R] H), g₁ * g₂ = g₂ * g₁) :
    Coalgebra.IsCocomm R H :=
  isCocomm_of_convMul_comm (hcomm _ _)

theorem flat_tensor_self {A : Type} [CommRing A] [Algebra R A] [Module.Flat R A] :
    Module.Flat R (A ⊗[R] A) :=
  inferInstance

theorem finitePresentation_tensor_self {A : Type} [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [Algebra.FiniteType R A] :
    Algebra.FinitePresentation R (A ⊗[R] A) :=
  Algebra.FinitePresentation.of_finiteType.mp
    (Algebra.FiniteType.trans ‹Algebra.FiniteType R A› (Algebra.FiniteType.baseChange A (A := A)))

theorem flat_hopfKer {A : Type} [CommRing A] [HopfAlgebra R A] {B : Type} [CommRing B]
    [HopfAlgebra R B] [IsDedekindDomain R] [Module.Flat R A] (π : A →ₐc[R] B) :
    Module.Flat R ↥(HopfAlgebra.hopfKer π) :=
  inferInstance

end Cocomm

section Affine

variable (T : Type) [CommRing T]

def structureMap : Spec (CommRingCat.of T) ⟶ specInt :=
  Spec.map (CommRingCat.ofHom (algebraMap ℤ T))

scoped instance flat_structureMap [Module.Flat ℤ T] : Flat (structureMap T) := by
  rw [structureMap, HasRingHomProperty.Spec_iff (P := @Flat), CommRingCat.hom_ofHom,
    RingHom.flat_algebraMap_iff]
  infer_instance

scoped instance lfp_structureMap [Algebra.FinitePresentation ℤ T] :
    LocallyOfFinitePresentation (structureMap T) := by
  rw [structureMap, HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation),
    CommRingCat.hom_ofHom, RingHom.finitePresentation_algebraMap]
  infer_instance

variable [Module.Flat ℤ T] [Algebra.FinitePresentation ℤ T]

def affineObj : specInt.Fppf := Scheme.Fppf.mk (structureMap T)

def ΓAffineObj : Γ((affineObj T).left, ⊤) ≃+* T :=
  (Scheme.ΓSpecIso (CommRingCat.of T)).commRingCatIsoToRingEquiv

end Affine

section Flag

open Opposite

variable {p : ℕ} [Fact p.Prime] {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    {C : JZeroNeronPrimaryTorsionCore p q A hA} {m : ℕ}
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (j : Fin (flag.n + 1))

theorem convMul_comm_sections (U : specInt.Fppf)
    (g₁ g₂ : WithConv (flag.G j →ₐ[ℤ] Γ(U.left, ⊤))) : g₁ * g₂ = g₂ * g₁ := by
  let e := flag.F_sectionsEquiv j U
  obtain ⟨s₁, rfl⟩ : ∃ s, Additive.toMul (e s) = g₁ := ⟨e.symm (Additive.ofMul g₁), by simp⟩
  obtain ⟨s₂, rfl⟩ : ∃ s, Additive.toMul (e s) = g₂ := ⟨e.symm (Additive.ofMul g₂), by simp⟩
  rw [← toMul_add, ← toMul_add, ← map_add, ← map_add, add_comm]

theorem convMul_comm_points (T : Type) [CommRing T] (instT : Algebra ℤ T)
    (hflat : @Module.Flat ℤ T _ _ instT.toModule)
    (hfp : @Algebra.FinitePresentation ℤ T _ _ instT)
    (g₁ g₂ : WithConv (@AlgHom ℤ (flag.G j) T _ _ _ _ instT)) :
    g₁ * g₂ = g₂ * g₁ := by
  obtain rfl : instT = Ring.toIntAlgebra T := Subsingleton.elim _ _
  haveI := hflat
  haveI := hfp
  let U : specInt.Fppf := affineObj T
  let e : Γ(U.left, ⊤) ≃+* T := ΓAffineObj T
  let eA : Γ(U.left, ⊤) →ₐ[ℤ] T := e.toRingHom.toIntAlgHom
  let eI : T →ₐ[ℤ] Γ(U.left, ⊤) := e.symm.toRingHom.toIntAlgHom
  have heAI : ∀ x, eA (eI x) = x := fun x => e.apply_symm_apply x

  let G₁ : WithConv (flag.G j →ₐ[ℤ] Γ(U.left, ⊤)) := WithConv.toConv (eI.comp g₁.ofConv)
  let G₂ : WithConv (flag.G j →ₐ[ℤ] Γ(U.left, ⊤)) := WithConv.toConv (eI.comp g₂.ofConv)
  have h₁ : eA.comp G₁.ofConv = g₁.ofConv := by
    apply AlgHom.ext
    intro x
    exact heAI _
  have h₂ : eA.comp G₂.ofConv = g₂.ofConv := by
    apply AlgHom.ext
    intro x
    exact heAI _
  have hcomm := convMul_comm_sections flag j U G₁ G₂
  have h12 : eA.comp (G₁ * G₂).ofConv = (g₁ * g₂).ofConv := by
    rw [AlgHom.comp_convMul_distrib, h₁, h₂]
  have h21 : eA.comp (G₂ * G₁).ofConv = (g₂ * g₁).ofConv := by
    rw [AlgHom.comp_convMul_distrib, h₁, h₂]
  rw [hcomm] at h12
  exact WithConv.ofConv_injective (h12.symm.trans h21)

theorem flat_transport {M : Type} [AddCommGroup M] {m₁ m₂ : Module ℤ M}
    (h : @Module.Flat ℤ M _ _ m₁) : @Module.Flat ℤ M _ _ m₂ := by
  obtain rfl : m₁ = m₂ := Subsingleton.elim _ _
  exact h

theorem finiteType_transport {M : Type} [CommRing M] {a₁ a₂ : Algebra ℤ M}
    (h : @Algebra.FiniteType ℤ M _ _ a₁) : @Algebra.FiniteType ℤ M _ _ a₂ := by
  obtain rfl : a₁ = a₂ := Subsingleton.elim _ _
  exact h

theorem isCocomm_G :
    @Coalgebra.IsCocomm ℤ (flag.G j) _ _ Algebra.toModule Bialgebra.toCoalgebra := by
  have hflatG : @Module.Flat ℤ (flag.G j) _ _ Algebra.toModule :=
    flat_transport (flag.instFlat_G j)
  have hftG : @Algebra.FiniteType ℤ (flag.G j) _ _ Bialgebra.toAlgebra :=
    finiteType_transport (flag.instFiniteType_G j)

  refine isCocomm_of_points_comm (R := ℤ) (H := flag.G j) fun g₁ g₂ => ?_
  exact convMul_comm_points flag j _ _
    (flat_transport (flat_tensor_self (R := ℤ) (A := flag.G j)))
    (finitePresentation_tensor_self (R := ℤ) (A := flag.G j)) g₁ g₂

theorem flag_sectionsNat {U V : specInt.Fppf} (f : U ⟶ V)
    (s : (flag.F j).1.obj (op V)) (a : flag.G j) :
    (Additive.toMul (flag.F_sectionsEquiv j U ((flag.F j).1.map f.op s))) a =
      (Scheme.Γ.map f.left.op) ((Additive.toMul (flag.F_sectionsEquiv j V s)) a) := by
  obtain ⟨h, rfl⟩ := flag.π_surj j a
  have h1 := flag.F_sectionsCompat j U ((flag.F j).1.map f.op s) h
  have h2 := flag.F_sectionsCompat j V s h
  have hnat : (flag.ι j).1.app (op U) ((flag.F j).1.map f.op s) =
      (C.𝒥 m).1.map f.op ((flag.ι j).1.app (op V) s) := by
    exact ConcreteCategory.congr_hom ((flag.ι j).1.naturality f.op) s
  have h3 := C.sectionsNat m f ((flag.ι j).1.app (op V) s) h
  change WithConv.ofConv (Additive.toMul (flag.F_sectionsEquiv j U ((flag.F j).1.map f.op s)))
      (flag.π j h) =
    (Scheme.Γ.map f.left.op) (WithConv.ofConv (Additive.toMul (flag.F_sectionsEquiv j V s))
      (flag.π j h))
  rw [← h1, ← h2, hnat]
  exact h3

theorem flag_incl_sections (i : Fin flag.n) (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hqc : (qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i)
    (U : specInt.Fppf) (s : (flag.F i.castSucc).1.obj (op U)) (a : flag.G i.succ) :
    (Additive.toMul (flag.F_sectionsEquiv i.succ U ((flag.incl i).1.app (op U) s))) a =
      (Additive.toMul (flag.F_sectionsEquiv i.castSucc U s)) (qc a) := by
  obtain ⟨h, rfl⟩ := flag.π_surj i.succ a
  have h1 := flag.F_sectionsCompat i.succ U ((flag.incl i).1.app (op U) s) h
  have h2 := flag.F_sectionsCompat i.castSucc U s h
  have hι : (flag.ι i.succ).1.app (op U) ((flag.incl i).1.app (op U) s) =
      (flag.ι i.castSucc).1.app (op U) s := by
    simpa using
      ConcreteCategory.congr_hom (congrArg (fun η => η.1.app (op U)) (flag.incl_ι i)) s
  have hq : flag.quot i (flag.π i.succ h) = flag.π i.castSucc h :=
    congrArg (fun φ : C.H m →ₐ[ℤ] flag.G i.castSucc => φ h) (flag.quot_π i)
  change WithConv.ofConv (Additive.toMul (flag.F_sectionsEquiv i.succ U
      ((flag.incl i).1.app (op U) s))) (flag.π i.succ h) =
    WithConv.ofConv (Additive.toMul (flag.F_sectionsEquiv i.castSucc U s))
      ((qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) (flag.π i.succ h))
  rw [← h1, hι, h2, hqc, hq]

end Flag

end PrimaryLayerKernelReduction
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv.PrimaryLayerKernelReduction"

end
p2m_reactivate "P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv.PrimaryLayerKernelReduction"

open PrimaryLayerKernelReduction in

theorem solution
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (C : JZeroNeronPrimaryTorsionCore p q A hA) (m : ℕ)
    (flag : JZeroNeronPrimaryTorsionFlag p q A hA C m) (i : Fin flag.n)
    (qc : flag.G i.succ →ₐc[ℤ] flag.G i.castSucc)
    (hqc : (qc : flag.G i.succ →ₐ[ℤ] flag.G i.castSucc) = flag.quot i)
    (L : Sheaf (smallFppfTopology specInt) Ab.{1})
    (pr : flag.F i.succ ⟶ L) (hzero : flag.incl i ≫ pr = 0)
    (hses : (ShortComplex.mk (flag.incl i) pr hzero).ShortExact) :
    ∃ (K : Type) (_ : CommRing K) (_ : HopfAlgebra ℤ K) (_ : Algebra.FiniteType ℤ K)
      (_ : Module.Flat ℤ K) (j : K →ₐc[ℤ] flag.G i.succ)
      (e : ∀ U : specInt.Fppf,
        L.1.obj (Opposite.op U) ≃+ Additive (WithConv (K →ₐ[ℤ] Γ(U.left, ⊤)))),
      Function.Injective j ∧
      (j : K →ₐ[ℤ] flag.G i.succ).range = HopfAlgebra.hopfKer qc ∧
      HopfAlgebra.IsHopfGalois qc ∧
      Module.FaithfullyFlat ↥(HopfAlgebra.hopfKer qc) (flag.G i.succ) ∧
      (∀ {U V : specInt.Fppf} (f : U ⟶ V) (s : L.1.obj (Opposite.op V)) (k : K),
        (Additive.toMul (e U (L.1.map f.op s))) k
          = (Scheme.Γ.map f.left.op) ((Additive.toMul (e V s)) k)) := by

  have hsurj : Function.Surjective qc := by
    have h := flag.quot_surj i
    rwa [← hqc] at h

  haveI : @Module.Flat ℤ (flag.G i.succ) _ _ Algebra.toModule :=
    flat_transport (flag.instFlat_G i.succ)
  haveI : @Module.Flat ℤ (flag.G i.castSucc) _ _ Algebra.toModule :=
    flat_transport (flag.instFlat_G i.castSucc)
  haveI : @Algebra.FiniteType ℤ (flag.G i.succ) _ _ Bialgebra.toAlgebra :=
    finiteType_transport (flag.instFiniteType_G i.succ)

  haveI := isCocomm_G flag i.succ

  haveI hKflat := flat_hopfKer (R := ℤ) qc

  obtain ⟨hHG, hff, hft⟩ :=
    HopfAlgebra.isHopfGalois_and_faithfullyFlat_and_finiteType_hopfKer_of_surjective
      ℤ (flag.G i.succ) (flag.G i.castSucc) qc hsurj
  haveI := hft

  have hrange : ((HopfAlgebra.hopfKerVal qc : ↥(HopfAlgebra.hopfKer qc) →ₐc[ℤ] flag.G i.succ) :
      ↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] flag.G i.succ).range = HopfAlgebra.hopfKer qc := by
    have hval : ((HopfAlgebra.hopfKerVal qc : ↥(HopfAlgebra.hopfKer qc) →ₐc[ℤ] flag.G i.succ) :
        ↥(HopfAlgebra.hopfKer qc) →ₐ[ℤ] flag.G i.succ) = (HopfAlgebra.hopfKer qc).val := by
      ext s
      rfl
    rw [hval]
    exact Subalgebra.range_val _

  obtain ⟨e, -, enat⟩ :=
    AlgebraicGeometry.Scheme.exists_sectionsEquiv_of_shortExact_of_range_eq_hopfKer_of_isHopfGalois
      specInt (flag.G i.succ) (flag.G i.castSucc) qc ↥(HopfAlgebra.hopfKer qc)
      (HopfAlgebra.hopfKerVal qc) (HopfAlgebra.hopfKerVal_injective qc) hrange hHG hff
      (flag.F i.castSucc) (flag.F i.succ) L (flag.incl i) pr hzero hses
      (flag.F_sectionsEquiv i.succ) (fun f s a => flag_sectionsNat flag i.succ f s a)
      (flag.F_sectionsEquiv i.castSucc) (fun U s a => flag_incl_sections flag i qc hqc U s a)
  exact ⟨↥(HopfAlgebra.hopfKer qc), inferInstance, inferInstance, finiteType_transport hft,
    flat_transport hKflat, HopfAlgebra.hopfKerVal qc, e, HopfAlgebra.hopfKerVal_injective qc,
    hrange, hHG, hff, enat⟩

end S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv
end P2MW
export P2MW.S_ModularCurve_JZeroNeronPrimaryTorsionFlag_exists_hopfAlgebra_range_eq_hopfKer_sectionsEquiv (solution)
